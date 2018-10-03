/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

//#define PREASSIGN
//#define CHECK_LEARNED_CLAUSES_FOR_CONFLICT
//#define LEARN_ANTECEDENT_CLAUSES
//#define FILTERING_STATS
//#define MIXED

#ifdef FILTERING_STATS
int nconfs[4] = {};
int ABconfs = 0;
int ACconfs = 0;
int ADconfs = 0;
int BCconfs = 0;
int BDconfs = 0;
int CDconfs = 0;
int ABCconfs = 0;
int ABDconfs = 0;
int ACDconfs = 0;
int BCDconfs = 0;
int ABCDconfs = 0;
#endif

#if defined(PREASSIGN) || defined(LEARN_ANTECEDENT_CLAUSES)
#include <NTL/mat_GF2.h>
using namespace NTL;
#endif

#include <math.h>

#ifndef NDEBUG
#define PRINTCONF
#endif

#include "mtl/Sort.h"
#include "core/Solver.h"

#include <fftw3.h>

FILE* exhaustfile;

double* fft_signal;
fftw_complex* fft_result;
fftw_plan plan;

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

#if BRANCHING_HEURISTIC == CHB || BRANCHING_HEURISTIC == LRB
static DoubleOption  opt_step_size         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
#endif
#if BRANCHING_HEURISTIC == VSIDS
static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
#endif
#if ! LBD_BASED_CLAUSE_DELETION
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
#endif
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
#if BRANCHING_HEURISTIC == CHB
static DoubleOption  opt_reward_multiplier (_cat, "reward-multiplier", "Reward multiplier", 0.9, DoubleRange(0, true, 1, true));
#endif

static IntOption     opt_order     (_cat, "order",      "Order of matrix", -1, IntRange(-1, INT32_MAX));
static StringOption  opt_compstring(_cat, "compstring", "A string which contains a comma-separated list of the compression sums to be used.");
static BoolOption    opt_filtering (_cat, "filtering",  "Use PSD filtering programmatic check", false);
static StringOption  opt_exhaustive(_cat, "exhaustive", "Output for exhaustive search");

#ifdef PREASSIGN
bool seq_assigned[4] = {false, false, false, false};
double assigned_psds[4][99];
int assigned_pafs[4][99];
#endif

int div1, div2;
int compA[2][99];
int compB[2][99];
int compC[2][99];
int compD[2][99];
#ifdef PRINTCONF
void printclause(vec<Lit>& cl);
#endif
#ifdef PRINTLEARNT
void fprintclause(FILE* f, vec<Lit>& cl);
FILE* out_learnt_file;
#endif

int paf(int n, int* A, int s)
{   int ret = A[0]*A[s];
    for(int i=1; i<(n+1)/2; i++)
        ret += A[i]*(A[(i+s)%n]+A[(n+i-s)%n]);
    //for(int i=1; i<(n+1)/2; i++)
    //    ret += A[i]*A[(i+s)%n];
    //for(int i=1; i<(n+1)/2; i++)
    //    ret += A[i]*A[(n-i+s)%n];
    return ret;
}

inline int minindex(int n, int i)
{
  return (i <= n/2) ? i : n-i;
}

void Solver::generateXorClauses(const vec<Lit>& antecedent, const vec<Var>& vars, const int c)
{   const int n = vars.size();
    vec<Lit> clause;
    if(n==1)
        learnAntClause(antecedent, mkLit(vars[0], c==0));
    else if(n==2)
    {   if(c==0)
        {   learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], false));
            learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], true));
        }
        else if(c==1)
        {   learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], true));
            learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], false));
        }
    }
    else if(n==3)
    {   if(c==0)
        {   learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], true), mkLit(vars[2], true));
            learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], false), mkLit(vars[2], false));
            learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], true), mkLit(vars[2], false));
            learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], false), mkLit(vars[2], true));
        }
        else if(c==1)
        {   learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], false), mkLit(vars[2], false));
            learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], true), mkLit(vars[2], true));
            learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], false), mkLit(vars[2], true));
            learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], true), mkLit(vars[2], false));
        }
    }
    else if(n>3)
    {   Var tmp = newVar();
        learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], false), mkLit(tmp, false));
        learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], true), mkLit(tmp, false));
        learnAntClause(antecedent, mkLit(vars[0], false), mkLit(vars[1], false), mkLit(tmp, true));
        learnAntClause(antecedent, mkLit(vars[0], true), mkLit(vars[1], true), mkLit(tmp, true));
        for(int i=2; i<n; i++)
        {   tmp = newVar();
            learnAntClause(antecedent, mkLit(vars[i], true), mkLit(tmp-1, false), mkLit(tmp, false));
            learnAntClause(antecedent, mkLit(vars[i], false), mkLit(tmp-1, true), mkLit(tmp, false));
            learnAntClause(antecedent, mkLit(vars[i], false), mkLit(tmp-1, false), mkLit(tmp, true));
            learnAntClause(antecedent, mkLit(vars[i], true), mkLit(tmp-1, true), mkLit(tmp, true));
        }
        learnAntClause(antecedent, mkLit(tmp, c==0));
    }
}

void Solver::generateCompClauses(int n, int d, int i, int c, int v)
{
	int index = c*(n/2+1);

	if(v == -d)
	{	// all variables -1 variable
		for(int j=0; j<d; j++)
		{	vec<Lit> cl;
			int newindex = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			cl.clear();
			cl.push(mkLit(newindex, true));
			addClause(cl);
#ifdef PRINTCONF
			printclause(cl);
#endif
		}
	}
	else if(v == -d+2)
	{	// at least one 1 variable
		vec<Lit> cl;
		cl.clear();
		for(int j=0; j<d; j++)
		{
			int newindex = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			cl.push(mkLit(newindex, false));
		}
		addClause(cl);
#ifdef PRINTCONF
		printclause(cl);
#endif
		// at most one 1 variable
		for(int j=0; j<d; j++)
		{	
			int newindex_j = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			for(int k=j+1; k<d; k++)
			{	vec<Lit> cl;
				cl.clear();
				int newindex_k = index + (i+k*(n/d) <= n/2 ? i+k*(n/d) : n-i-k*(n/d));
				cl.push(mkLit(newindex_j, true));
				cl.push(mkLit(newindex_k, true));
				addClause(cl);
#ifdef PRINTCONF
				printclause(cl);
#endif
			}
		}
	}
	else if(v == -d+4)
	{	// at least two 1 variables
		for(int j=0; j<d; j++)
		{
			vec<Lit> cl;
			cl.clear();
			for(int k=0; k<d; k++)
			{	if(k==j)
					continue;
				int newindex = index + (i+k*(n/d) <= n/2 ? i+k*(n/d) : n-i-k*(n/d));
				cl.push(mkLit(newindex, false));
			}
			addClause(cl);
#ifdef PRINTCONF
			printclause(cl);
#endif
		}
		// at most two 1 variables
		for(int j=0; j<d; j++)
		{	int newindex_j = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			for(int k=j+1; k<d; k++)
			{	int newindex_k = index + (i+k*(n/d) <= n/2 ? i+k*(n/d) : n-i-k*(n/d));
				for(int l=k+1; l<d; l++)
				{	vec<Lit> cl;
					cl.clear();
					int newindex_l = index + (i+l*(n/d) <= n/2 ? i+l*(n/d) : n-i-l*(n/d));
					cl.push(mkLit(newindex_j, true));
					cl.push(mkLit(newindex_k, true));
					cl.push(mkLit(newindex_l, true));
					addClause(cl);
#ifdef PRINTCONF
					printclause(cl);
#endif
				}
			}
		}
	}
	else if(v == d-4)
	{	// at least two -1 variables
		for(int j=0; j<d; j++)
		{
			vec<Lit> cl;
			cl.clear();
			for(int k=0; k<d; k++)
			{	if(k==j)
					continue;
				int newindex = index + (i+k*(n/d) <= n/2 ? i+k*(n/d) : n-i-k*(n/d));
				cl.push(mkLit(newindex, true));
			}
			addClause(cl);
#ifdef PRINTCONF
			printclause(cl);
#endif
		}
		// at most two -1 variables
		for(int j=0; j<d; j++)
		{	int newindex_j = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			for(int k=j+1; k<d; k++)
			{	int newindex_k = index + (i+k*(n/d) <= n/2 ? i+k*(n/d) : n-i-k*(n/d));
				for(int l=k+1; l<d; l++)
				{	vec<Lit> cl;
					cl.clear();
					int newindex_l = index + (i+l*(n/d) <= n/2 ? i+l*(n/d) : n-i-l*(n/d));
					cl.push(mkLit(newindex_j, false));
					cl.push(mkLit(newindex_k, false));
					cl.push(mkLit(newindex_l, false));
					addClause(cl);
#ifdef PRINTCONF
					printclause(cl);
#endif
				}
			}
		}
	}
	else if(v == d-2)
	{	// at least one -1 variable
		vec<Lit> cl;
		cl.clear();
		for(int j=0; j<d; j++)
		{
			int newindex = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			cl.push(mkLit(newindex, true));
		}
		addClause(cl);
#ifdef PRINTCONF
		printclause(cl);
#endif
		// at most one -1 variable
		for(int j=0; j<d; j++)
		{	
			int newindex_j = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			for(int k=j+1; k<d; k++)
			{	vec<Lit> cl;
				cl.clear();
				int newindex_k = index + (i+k*(n/d) <= n/2 ? i+k*(n/d) : n-i-k*(n/d));
				cl.push(mkLit(newindex_j, false));
				cl.push(mkLit(newindex_k, false));
				addClause(cl);
#ifdef PRINTCONF
				printclause(cl);
#endif
			}
		}
	}
	else if(v == d)
	{	// all variables 1
		for(int j=0; j<d; j++)
		{	vec<Lit> cl;
			int newindex = index + (i+j*(n/d) <= n/2 ? i+j*(n/d) : n-i-j*(n/d));
			cl.clear();
			cl.push(mkLit(newindex, false));
			addClause(cl);
#ifdef PRINTCONF
			printclause(cl);
#endif
		}
	}
	
}

void Solver::addCompClauses()
{	//printf("compstring: %s\n", compstring);	
	if(compstring != NULL)
	{	
		char* tmp = (char*)compstring;

		if(sscanf(tmp, "%d", &div1) != 1)
			printf("ERROR! syntax error in compstring: %s\n", tmp), exit(1);

		while(*tmp != ',')
		{	if(*tmp == '\0')
				return;
			tmp++;
		}
		tmp++;

		bool hadzero;
		vec<Lit> cl;
		const int n = order;
		const int d = div1;
		
		hadzero = false;
		for(int i=0; i<order/div1; i++)
		{	sscanf(tmp, "%d", &compA[0][i]);
			if(d == 2 && compA[0][i] == 0 && hadzero == false)
			{	hadzero = true;
				cl.clear();
				cl.push(mkLit(i, false));
				addClause(cl);
				cl.clear();
				cl.push(mkLit(0*(n/2+1) + (i+(n/d) <= n/2 ? i+(n/d) : n-i-(n/d)), true));
				addClause(cl);
			}
			else
				generateCompClauses(order, div1, i, 0, compA[0][i]);
			while(*tmp != ',' && *tmp != '\0')
			{	tmp++;
			}
			if(*tmp != '\0')
				tmp++;
		}

#ifdef PREASSIGN
		if(d == 1 && opt_filtering)
		{	seq_assigned[0] = true;
			for(int i=0; i<order; i++)
			{	fft_signal[i] = compA[0][i];
			}
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				fft_signal[(n-i)%n] = fft_signal[i] = assigned_psds[0][i] = fft_result[i][0]*fft_result[i][0];
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				assigned_pafs[0][i] = (int)round(fft_result[i][0]/order);
		}
#endif

		if(*tmp == '\0')
			return;

		hadzero = false;
		for(int i=0; i<order/div1; i++)
		{	sscanf(tmp, "%d", &compB[0][i]);
			if(d == 2 && compB[0][i] == 0 && hadzero == false)
			{	hadzero = true;
				cl.clear();
				cl.push(mkLit(1*(n/2+1) + i, false));
				addClause(cl);
				cl.clear();
				cl.push(mkLit(1*(n/2+1) + (i+(n/d) <= n/2 ? i+(n/d) : n-i-(n/d)), true));
				addClause(cl);
			}
			else
				generateCompClauses(order, div1, i, 1, compB[0][i]);
			while(*tmp != ',' && *tmp != '\0')
			{	tmp++;
			}
			if(*tmp != '\0')
				tmp++;
		}

#ifdef PREASSIGN
		if(d == 1 && opt_filtering)
		{	seq_assigned[1] = true;
			for(int i=0; i<order; i++)
			{	fft_signal[i] = compB[0][i];
			}
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				fft_signal[(n-i)%n] = fft_signal[i] = assigned_psds[1][i] = fft_result[i][0]*fft_result[i][0];
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				assigned_pafs[1][i] = (int)round(fft_result[i][0]/order);
		    
			Mat<GF2> M;
			M.SetDims(n/2, n/2+1);

			for(int k=1; k<n/2+1; k++)
			{   printf("k=%d:", k);

			    int terms[n] = {};

			    for(int j=0; j<n; j++)
			    {   if(compA[0][j]*compB[0][j]*compA[0][(j+k)%n]*compB[0][(j+k)%n]==((j+k)%n==0 ? 1 : -1)*(j==0 ? 1 : -1))
				{   if(minindex(n,j) < minindex(n,(j+k)%n))
				    {   //printf(" + c[%d]*c[%d]", minindex(n, j), minindex(n, (j+k)%n));
					terms[minindex(n, j)]++;
					terms[minindex(n, (j+k)%n)]++;
					terms[0]--;
				    }
				}
			    }

			    int rhs = 0;

			    for(int j=1; j<n; j++)
			    {   if(terms[j]%2>0)
				    printf("+c[%d]", j);
				rhs += terms[j]%4;
			    }
			    printf("=%d\n", (rhs-terms[0]+(-(assigned_pafs[0][k]+assigned_pafs[1][k])/2-1)/2)/2);

			    for(int j=1; j<n; j++)
			    {   if(terms[j]%2>0)
				    M(k,j) = 1;
			    }
			    M(k,n/2+1) = ((rhs-terms[0]+(-(assigned_pafs[0][k]+assigned_pafs[1][k])/2-1)/2)/2)%2;
			    
			}

			std::cout << M << "\n";

			gauss(M);

			std::cout << M << "\n";

			long c=2;
			for(long j=2; j<n/2+1; j++)
			{   if(M(c, j)==1)
			    {   for(long k=1; k<c; k++)
				{   if(M(k, j)==1)
					M[k-1] += M[c-1];
				}
				c++;
			    }
			}

			std::cout << M << "\n";

			for(long k=0; k<n/2; k++)
			{   vec<Var> vars;
			    //vars.clear();
			    for(long j=0; j<n/2; j++)
			    {   if(M[k][j]==1)
				    vars.push(2*(n/2+1)+j+1);
			    }
			    if(vars.size()==0)
				continue;
			    //for(int j=0; j<vars.size(); j++)
			    //    printf("%d ", vars[j]+1);
			    //printf("= %d\n", IsZero(M[k][n/2]) ? 0 : 1);
			    vec<Lit> empty;
			    generateXorClauses(empty, vars, IsZero(M[k][n/2]) ? 0 : 1);
			}
		}
#endif

		if(*tmp == '\0')
			return;

		hadzero = false;
		for(int i=0; i<order/div1; i++)
		{	sscanf(tmp, "%d", &compC[0][i]);
			if(d == 2 && compC[0][i] == 0 && hadzero == false)
			{	hadzero = true;
				cl.clear();
				cl.push(mkLit(2*(n/2+1) + i, false));
				addClause(cl);
				cl.clear();
				cl.push(mkLit(2*(n/2+1) + (i+(n/d) <= n/2 ? i+(n/d) : n-i-(n/d)), true));
				addClause(cl);
			}
			else
				generateCompClauses(order, div1, i, 2, compC[0][i]);
			while(*tmp != ',' && *tmp != '\0')
			{	tmp++;
			}
			if(*tmp != '\0')
				tmp++;
		}

#ifdef PREASSIGN
		if(d == 1 && opt_filtering)
		{	seq_assigned[2] = true;
			for(int i=0; i<order; i++)
			{	fft_signal[i] = compC[0][i];
			}
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				fft_signal[(n-i)%n] = fft_signal[i] = assigned_psds[2][i] = fft_result[i][0]*fft_result[i][0];
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				assigned_pafs[2][i] = (int)round(fft_result[i][0]/order);
		}
#endif

		if(*tmp == '\0')
			return;

		hadzero = false;
#ifdef MIXED
		for(int i=0; i<order; i++)
#else
		for(int i=0; i<order/div1; i++)
#endif
		{	sscanf(tmp, "%d", &compD[0][i]);
			if(d == 2 && compD[0][i] == 0 && hadzero == false)
			{	hadzero = true;
				cl.clear();
				cl.push(mkLit(3*(n/2+1) + i, false));
				addClause(cl);
				cl.clear();
				cl.push(mkLit(3*(n/2+1) + (i+(n/d) <= n/2 ? i+(n/d) : n-i-(n/d)), true));
				addClause(cl);
			}
			else
#ifdef MIXED
				generateCompClauses(order, 1, i, 3, compD[0][i]);
#else
				generateCompClauses(order, div1, i, 3, compD[0][i]);
#endif
			while(*tmp != ',' && *tmp != '\0')
			{	tmp++;
			}
			if(*tmp != '\0')
				tmp++;
		}

#ifdef PREASSIGN
		if(d == 1 && opt_filtering)
		{	seq_assigned[3] = true;
			for(int i=0; i<order; i++)
			{	fft_signal[i] = compD[0][i];
			}
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				fft_signal[(n-i)%n] = fft_signal[i] = assigned_psds[3][i] = fft_result[i][0]*fft_result[i][0];
			fftw_execute(plan);
			for(int i=0; i<n/2+1; i++)
				assigned_pafs[3][i] = (int)round(fft_result[i][0]/order);
		}
#endif

		if(*tmp == '\0')
			return;

		if(sscanf(tmp, "%d", &div2) == 1)
		{
			while(*tmp != ',' && *tmp != '\0')
				tmp++;
			tmp++;

			for(int i=0; i<order/div2; i++)
			{	sscanf(tmp, "%d", &compA[0][i]);
				generateCompClauses(order, div2, i, 0, compA[0][i]);
				while(*tmp != ',' && *tmp != '\0')
					tmp++;
				tmp++;
			}

			for(int i=0; i<order/div2; i++)
			{	sscanf(tmp, "%d", &compB[0][i]);
				generateCompClauses(order, div2, i, 1, compB[0][i]);
				while(*tmp != ',' && *tmp != '\0')
					tmp++;
				tmp++;
			}

			for(int i=0; i<order/div2; i++)
			{	sscanf(tmp, "%d", &compC[0][i]);
				generateCompClauses(order, div2, i, 2, compC[0][i]);
				while(*tmp != ',' && *tmp != '\0')
					tmp++;
				tmp++;
			}

			for(int i=0; i<order/div2; i++)
			{	sscanf(tmp, "%d", &compD[0][i]);
				generateCompClauses(order, div2, i, 3, compD[0][i]);
				while(*tmp != ',' && *tmp != '\0')
					tmp++;
				tmp++;
			}

		}

	}
 
}

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
#if BRANCHING_HEURISTIC == CHB || BRANCHING_HEURISTIC == LRB
  , step_size        (opt_step_size)
  , step_size_dec    (opt_step_size_dec)
  , min_step_size    (opt_min_step_size)
#endif
#if BRANCHING_HEURISTIC == VSIDS
  , var_decay        (opt_var_decay)
#endif
#if ! LBD_BASED_CLAUSE_DELETION
  , clause_decay     (opt_clause_decay)
#endif
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  
  , lbd_calls(0)
#if BRANCHING_HEURISTIC == CHB
  , action(0)
  , reward_multiplier(opt_reward_multiplier)
#endif

  , order (opt_order) 
  , compstring (opt_compstring)
  , exhauststring (opt_exhaustive)
  , ok                 (true)
#if ! LBD_BASED_CLAUSE_DELETION
  , cla_inc            (1)
#endif
#if BRANCHING_HEURISTIC == VSIDS
  , var_inc            (1)
#endif
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{

    if(exhauststring != NULL)
    {   exhaustfile = fopen(exhauststring, "a");
    }

#ifdef PRINTLEARNT
    out_learnt_file = fopen("out_learnt_file", "w");
#endif

	if(opt_filtering)
	{	if(order == -1)
			printf("need to set order\n"), exit(1);
		fft_signal = (double*)malloc(sizeof(double)*order);
		fft_result = (fftw_complex*)malloc(sizeof(fftw_complex)*order);
		plan = fftw_plan_dft_r2c_1d(order, fft_signal, fft_result, FFTW_ESTIMATE);
	}

}


Solver::~Solver()
{
    if(opt_filtering)
    {   fftw_destroy_plan(plan);
        free(fft_signal);
        free(fft_result);
    }

    if(exhauststring != NULL)
    {   fclose(exhaustfile);
    }

#ifdef PRINTLEARNT
    fclose(out_learnt_file);
#endif
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    lbd_seen.push(0);
    picked.push(0);
    conflicted.push(0);
#if ALMOST_CONFLICT
    almost_conflicted.push(0);
#endif
#if ANTI_EXPLORATION
    canceled.push(0);
#endif
#if BRANCHING_HEURISTIC == CHB
    last_conflict.push(0);
#endif
    total_actual_rewards.push(0);
    total_actual_count.push(0);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}

#ifdef CHECK_LEARNED_CLAUSES_FOR_CONFLICT
bool Solver::notInConflict(const vec<Lit>& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            return true;
    return false; }
#endif

bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            uint64_t age = conflicts - picked[x];
            if (age > 0) {
                double reward = ((double) conflicted[x]) / ((double) age);
#if BRANCHING_HEURISTIC == LRB
#if ALMOST_CONFLICT
                double adjusted_reward = ((double) (conflicted[x] + almost_conflicted[x])) / ((double) age);
#else
                double adjusted_reward = reward;
#endif
                double old_activity = activity[x];
                activity[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
                if (order_heap.inHeap(x)) {
                    if (activity[x] > old_activity)
                        order_heap.decrease(x);
                    else
                        order_heap.increase(x);
                }
#endif
                total_actual_rewards[x] += reward;
                total_actual_count[x] ++;
            }
#if ANTI_EXPLORATION
            canceled[x] = conflicts;
#endif
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        } else {
#if ANTI_EXPLORATION
            next = order_heap[0];
            uint64_t age = conflicts - canceled[next];
            while (age > 0 && value(next) == l_Undef) {
                double decay = pow(0.95, age);
                activity[next] *= decay;
                if (order_heap.inHeap(next)) {
                    order_heap.increase(next);
                }
                canceled[next] = conflicts;
                next = order_heap[0];
                age = conflicts - canceled[next];
            }
#endif
            next = order_heap.removeMin();
        }

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}

#ifdef PRINTCONF
void printclause(vec<Lit>& cl)
{ printf("clause size %d: ", cl.size());
  for(int i=0; i<cl.size(); i++)
  { printf("%c%d ", sign(cl[i]) ? '-' : '+', var(cl[i])+1);
  }
  printf("\n");
}
#endif
#ifdef PRINTLEARNT
void fprintclause(FILE* f, vec<Lit>& cl)
{ 
  for(int i=0; i<cl.size(); i++)
  { fprintf(f, "%s%d ", sign(cl[i]) ? "-" : "", var(cl[i])+1);
  }
  fprintf(f, "0\n");
}
#endif

// A callback function for programmatic interface. If the callback detects conflicts, then
// refine the clause database by adding clauses to out_learnts. This function is called
// very frequently, if the analysis is expensive then add code to skip the analysis on
// most calls. However, if complete is set to true, do not skip the analysis or else the
// solver will be unsound.
//
// complete: true if and only if the current trail is a complete assignment that satisfies
//           the clause database. Note that not every variable is necessarily assigned since
//           the simplification steps may have removed some variables! If complete is true,
//           the solver will return satisfiable immediately unless this function returns at
//           least one clause.
void Solver::callbackFunction(bool complete, vec<vec<Lit> >& out_learnts) {
    if(order==-1)
        return;

    if(opt_filtering || exhauststring != NULL)
    {   filtering_check(out_learnts);
    }
    
#ifdef PRINTCONF
    for(int i=0; i<out_learnts.size(); i++)
    {   printf("learned clause %d: ", i);
        printclause(out_learnts[i]);
    }
    if(out_learnts.size()==0)
        printf("no learned clauses\n");
#endif

}

void Solver::learnAntClause(const vec<Lit>& ant, Lit p)
{
    vec<Lit> learnt_clause;
    ant.copyTo(learnt_clause);
    learnt_clause.push(p);

    CRef cr = ca.alloc(learnt_clause, true);
    learnts.push(cr);
    attachClause(cr);
#if LBD_BASED_CLAUSE_DELETION
    Clause& clause = ca[cr];
    clause.activity() = lbd(clause);
#else
    claBumpActivity(ca[cr]);
#endif
}

void Solver::learnAntClause(const vec<Lit>& ant, Lit p, Lit q)
{
    vec<Lit> learnt_clause;
    ant.copyTo(learnt_clause);
    learnt_clause.push(p);
    learnt_clause.push(q);

    CRef cr = ca.alloc(learnt_clause, true);
    learnts.push(cr);
    attachClause(cr);
#if LBD_BASED_CLAUSE_DELETION
    Clause& clause = ca[cr];
    clause.activity() = lbd(clause);
#else
    claBumpActivity(ca[cr]);
#endif
}

void Solver::learnAntClause(const vec<Lit>& ant, Lit p, Lit q, Lit r)
{
    vec<Lit> learnt_clause;
    ant.copyTo(learnt_clause);
    learnt_clause.push(p);
    learnt_clause.push(q);
    learnt_clause.push(r);

    CRef cr = ca.alloc(learnt_clause, true);
    learnts.push(cr);
    attachClause(cr);
#if LBD_BASED_CLAUSE_DELETION
    Clause& clause = ca[cr];
    clause.activity() = lbd(clause);
#else
    claBumpActivity(ca[cr]);
#endif
}

struct psd_holder {
	int seqindex;
	double psd;
};

void swap_psd_holders(struct psd_holder* x, struct psd_holder* y)
{ struct psd_holder tmp = *x;
  *x = *y;
  *y = tmp;
}

void Solver::filtering_check(vec<vec<Lit> >& out_learnts)
{
  const int n = order;
  const int dim = n/2+1;
  bool allseqcomplete = true;
  
  struct psd_holder psds[dim][4];
#ifdef LEARN_ANTECEDENT_CLAUSES
  double C_psds[dim];
  double D_psds[dim];
  int C_entries[n] = {};
  int D_entries[n] = {};
#endif

  double psdsum[dim];
  for(int i=0; i<dim; i++)
    psdsum[i] = 0;

  /*for(int seq=0; seq<4; seq++)
  { for(int i=0; i<dim; i++)
    { if(assigns[i+seq*dim] == l_Undef)
        printf("?");
      if(assigns[i+seq*dim] == l_True)
        printf("+");
      if(assigns[i+seq*dim] == l_False)
        printf("-");
    }
    printf(" ");
  }
  printf("\n");*/

  for(int seq=0; seq<4; seq++)
  { 
    bool seqcomplete = true;
    for(int i=seq*dim; i<(seq+1)*dim; i++)
    { if(assigns[i] == l_Undef)
      { allseqcomplete = seqcomplete = false;
        break;
      }
    }

    if(!opt_filtering)
      continue;

    if(seqcomplete)
    { 

#ifdef PREASSIGN
      if(!seq_assigned[seq])
#endif
      {
        fft_signal[0] = (assigns[seq*dim] == l_True) ? 1 : -1;
        for(int i=1; i<dim; i++)
            fft_signal[n-i] = fft_signal[i] = (assigns[i+seq*dim] == l_True) ? 1 : -1;

        fftw_execute(plan);

#ifdef LEARN_ANTECEDENT_CLAUSES
        if(seq==2)
        {   for(int i=0; i<n; i++)
                C_entries[i] = fft_signal[i];
        }
        else if(seq==3)
        {   for(int i=0; i<n; i++)
                D_entries[i] = fft_signal[i];
        }
#endif
      }

      for(int i=0; i<dim; i++)
      { 
        double psd_i;

#ifdef PREASSIGN
        if(seq_assigned[seq])
            psd_i = assigned_psds[seq][i];
        else
#endif
            psd_i = fft_result[i][0]*fft_result[i][0];

#ifdef LEARN_ANTECEDENT_CLAUSES
        if(seq==2)
            C_psds[i] = psd_i;
        else if(seq==3)
            D_psds[i] = psd_i;
#endif

        psds[i][seq].seqindex = seq;
        psds[i][seq].psd = psd_i;
        psdsum[i] += psd_i;

        if(psdsum[i] > 4*n+0.01)
        { 
          // Sort PSDs
#ifdef DEBUG
          printf("filtering PSDs before: ");
          for(int s=0; s<seq+1; s++)
            printf("%.2f ", psds[i][s].psd);
          printf("\n");
#endif

          if(seq==1)
          { if(psds[i][0].psd < psds[i][1].psd)
              swap_psd_holders(psds[i], psds[i]+1);
          }
          else if(seq==2)
          { if(psds[i][1].psd < psds[i][2].psd)
              swap_psd_holders(psds[i]+1, psds[i]+2);
            if(psds[i][0].psd < psds[i][1].psd)
              swap_psd_holders(psds[i], psds[i]+1);
            if(psds[i][1].psd < psds[i][2].psd)
              swap_psd_holders(psds[i]+1, psds[i]+2);
          }
          else if(seq==3)
          { if(psds[i][0].psd < psds[i][1].psd)
              swap_psd_holders(psds[i], psds[i]+1);
            if(psds[i][2].psd < psds[i][3].psd)
              swap_psd_holders(psds[i]+2, psds[i]+3);
            if(psds[i][0].psd < psds[i][2].psd)
              swap_psd_holders(psds[i], psds[i]+2);
            if(psds[i][1].psd < psds[i][2].psd)
              swap_psd_holders(psds[i]+1, psds[i]+2);
            if(psds[i][1].psd < psds[i][3].psd)
              swap_psd_holders(psds[i]+1, psds[i]+3);
            if(psds[i][2].psd < psds[i][3].psd)
              swap_psd_holders(psds[i]+2, psds[i]+3);
          }

#ifdef DEBUG
          printf("filtering PSDs after: ");
          for(int s=0; s<seq+1; s++)
            printf("%.2f ", psds[i][s].psd);
          printf("\n");
#endif
          double this_psdsum = 0;
          bool seqused[4] = {false, false, false, false};

          for(int seq=0; seq<4; seq++)
          { 
             assert(psds[i][seq].seqindex >= 0);
             seqused[psds[i][seq].seqindex] = true;
#ifdef NDEBUG
             this_psdsum += psds[i][seq].psd;
#else
             double psd_i_alt;
             int seqindex = psds[i][seq].seqindex;
             if(assigns[seqindex*dim] == l_True)
               psd_i_alt = 1;
             else
               psd_i_alt = -1;
             for(int k=1; k<n/2+(n%2 == 0 ? 0 : 1); k++)
             { if(assigns[k+seqindex*dim] == l_True)
                 psd_i_alt += 2*cosarray[n][(i*k)%n];
               else
                 psd_i_alt -= 2*cosarray[n][(i*k)%n];
             }
             if(n%2==0)
             { if(assigns[n/2+seqindex*dim] == l_True)
                 psd_i_alt += (i % 2 == 0 ? 1 : -1);
               else
                 psd_i_alt -= (i % 2 == 0 ? 1 : -1);
             }
             psd_i_alt *= psd_i_alt;
             this_psdsum += psd_i_alt;
#endif
             
             assert(abs(psds[i][seq].psd-psd_i_alt) < 0.0001);

             if(this_psdsum > 4*n + 0.01)
             {

                int size = out_learnts.size();
                out_learnts.push();
                //vec<Lit> cl;
                //cl.clear();

                for(int s=0; s<4; s++)
                {
                  if(seqused[s])
                  { for(int j=s*dim; j<(s+1)*dim; j++)
                    { if(assigns[j] == l_True)
                      { out_learnts[size].push(mkLit(j, true)) /*, printf("+")*/;
                        //cl.push(mkLit(j, true));
                      }
                      else if(assigns[j] == l_False)
                      { out_learnts[size].push(mkLit(j, false))/*, printf("-")*/;
                        //cl.push(mkLit(j, false));
                      }
                    }
                  }
                  //printf(" ");
                }
                //printf("\n");
#ifdef FILTERING_STATS
		if(seqused[0] && seqused[1] && seqused[2] && seqused[3])
			ABCDconfs++;
		else if(seqused[0] && seqused[1] && seqused[2])
			ABCconfs++;
		else if(seqused[0] && seqused[1] && seqused[3])
			ABDconfs++;
		else if(seqused[0] && seqused[2] && seqused[3])
			ACDconfs++;
		else if(seqused[1] && seqused[2] && seqused[3])
			BCDconfs++;
		else if(seqused[0] && seqused[1])
			ABconfs++;
		else if(seqused[0] && seqused[2])
			ACconfs++;
		else if(seqused[0] && seqused[3])
			ADconfs++;
		else if(seqused[1] && seqused[2])
			BCconfs++;
		else if(seqused[1] && seqused[3])
			BDconfs++;
		else if(seqused[2] && seqused[3])
			CDconfs++;
		else if(seqused[0])
			nconfs[0]++;
		else if(seqused[1])
			nconfs[1]++;
		else if(seqused[2])
			nconfs[2]++;
		else if(seqused[3])
			nconfs[3]++;
#endif

#ifdef PRINTLEARNT
                fprintclause(out_learnt_file, out_learnts[size]);
#endif

#ifdef PRINTCONF
                printf("out_learnt "), printclause(out_learnts[size]);
#endif

                return;

             }
          }

        }

      }

    }
    else
    {  for(int i=0; i<dim; i++)
       {  psds[i][seq].seqindex = -1;
          psds[i][seq].psd = -1;
       }
    }
  }

#ifdef LEARN_ANTECEDENT_CLAUSES
  if(C_entries[0] != 0 && D_entries[0] != 0)
#endif
  { /*printf("PSDs: ");
    for(int i=0; i<dim; i++)
       {  printf("%.2f ", psdsum[i]);
       }*/

    /*printf("Solution: ");
    for(int k=0; k<4; k++)
    { for(int i=0; i<dim; i++)
        printf("%c", (assigns[k*dim+i] == l_True) ? '+' : '-');
      printf(" ");
    }
    printf("\n");*/


    if(allseqcomplete && exhauststring != NULL)
    {
      for(int k=0; k<4; k++)
      { for(int i=0; i<n; i++)
        { int index = minindex(n, i);
          fprintf(exhaustfile, "%s ", (assigns[k*dim+index] == l_True) ? "1" : "-1");
        }
      }
      fprintf(exhaustfile, "\n");

      int size = out_learnts.size();
      out_learnts.push();

      for(int s=0; s<4; s++)
      {
        for(int j=s*dim; j<(s+1)*dim; j++)
        { if(assigns[j] == l_True)
            out_learnts[size].push(mkLit(j, true));
          else if(assigns[j] == l_False)
            out_learnts[size].push(mkLit(j, false));
        }
      }
#ifdef PRINTCONF
      printf("out_learnt "), printclause(out_learnts[size]);
#endif
    }

#ifdef LEARN_ANTECEDENT_CLAUSES
    vec<Lit> antecedent;

    for(int s=2; s<4; s++)
    {
      for(int j=s*dim; j<(s+1)*dim; j++)
      { if(assigns[j] == l_True)
          antecedent.push(mkLit(j, true));
        else if(assigns[j] == l_False)
          antecedent.push(mkLit(j, false));
      }
    }

#ifdef PRINTCONF
    printf("antecedent ");
    printclause(antecedent);
#endif

    int C_pafs[dim];
    int D_pafs[dim];

    fft_signal[0] = C_psds[0];
    for(int i=1; i<dim; i++)
        fft_signal[n-i] = fft_signal[i] = C_psds[i];
    fftw_execute(plan);
    for(int i=0; i<n/2+1; i++)
        C_pafs[i] = (int)round(fft_result[i][0]/n);

    fft_signal[0] = D_psds[0];
    for(int i=1; i<dim; i++)
        fft_signal[n-i] = fft_signal[i] = D_psds[i];
    fftw_execute(plan);
    for(int i=0; i<n/2+1; i++)
        D_pafs[i] = (int)round(fft_result[i][0]/n);

    /*printf("PAFs: ");
    for(int i=0; i<=n/2; i++)
    {   printf("%d ", C_pafs[i]);
    }
    printf("\n");*/

    Mat<GF2> M;
    M.SetDims(n/2, n/2+1);

    for(int k=1; k<n/2+1; k++)
    {   int terms[n] = {};

        for(int j=0; j<n; j++)
        {   if(C_entries[j]*D_entries[j]*C_entries[(j+k)%n]*D_entries[(j+k)%n]==((j+k)%n==0 ? 1 : -1)*(j==0 ? 1 : -1))
            {   if(minindex(n,j) < minindex(n,(j+k)%n))
                {   //printf(" + c[%d]*c[%d]", minindex(n, j), minindex(n, (j+k)%n));
                    terms[minindex(n, j)]++;
                    terms[minindex(n, (j+k)%n)]++;
                    terms[0]--;
                }
            }
        }

        int rhs = 0;
        for(int j=1; j<n; j++)
            rhs += terms[j]%4;

        for(int j=1; j<n; j++)
        {   if(terms[j]%2>0)
                M(k,j) = 1;
        }
        M(k,n/2+1) = ((rhs-terms[0]+(-(C_pafs[k]+D_pafs[k])/2-1)/2)/2)%2;
    }

    gauss(M);

    long c=2;
    for(long j=2; j<n/2+1; j++)
    {   if(M(c, j)==1)
        {   for(long k=1; k<c; k++)
            {   if(M(k, j)==1)
                    M[k-1] += M[c-1];
            }
            c++;
        }
    }

    for(long k=0; k<n/2; k++)
    {   vec<Var> vars;
        for(long j=0; j<n/2; j++)
        {   if(IsOne(M[k][j]))
                vars.push(j+1);
        }
        generateXorClauses(antecedent, vars, IsZero(M[k][n/2]) ? 0 : 1);
    }
#endif
  }

}

bool Solver::assertingClause(CRef confl) {
    Clause& c = ca[confl];
    int asserting = -1;
    for (int i = 0; i < c.size(); i++) {
        if (value(c[i]) == l_Undef) {
            if (asserting != -1) return false;
            asserting = i;
        }
    }
    return asserting == 0;
}

void Solver::analyze(vec<Lit>& conflvec, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    CRef confl;
    Lit p     = lit_Undef;

    int cur_max = level(var(conflvec[0]));
    for(int j=1; j < conflvec.size(); j++) {
        if(level(var(conflvec[j])) > cur_max) {
            cur_max = level(var(conflvec[j]));
        }
    }
    if(cur_max == 0) {
        out_btlevel = -1;
        return;
    }
    if (conflvec.size() == 1) {
        out_btlevel = 0;
        conflvec.copyTo(out_learnt);
        return;
    }

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

        for (int j = (p == lit_Undef) ? 0 : 1; j < conflvec.size(); j++){
            Lit q = conflvec[j];

            if (!seen[var(q)] && level(var(q)) > 0){
#if BRANCHING_HEURISTIC == CHB
                last_conflict[var(q)] = conflicts;
#elif BRANCHING_HEURISTIC == VSIDS
                varBumpActivity(var(q));
#endif
                conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= cur_max)
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    while(pathC > 0){
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

#if LBD_BASED_CLAUSE_DELETION
        if (c.learnt() && c.activity() > 2)
            c.activity() = lbd(c);
#else
        if (c.learnt())
            claBumpActivity(c);
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
#if BRANCHING_HEURISTIC == CHB
                last_conflict[var(q)] = conflicts;
#elif BRANCHING_HEURISTIC == VSIDS
                varBumpActivity(var(q));
#endif
                conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= cur_max)
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

#if ALMOST_CONFLICT
    seen[var(p)] = true;
    for(int i = out_learnt.size() - 1; i >= 0; i--) {
        Var v = var(out_learnt[i]);
        CRef rea = reason(v);
        if (rea != CRef_Undef) {
            Clause& reaC = ca[rea];
            for (int i = 0; i < reaC.size(); i++) {
                Lit l = reaC[i];
                if (!seen[var(l)]) {
                    seen[var(l)] = true;
                    almost_conflicted[var(l)]++;
                    analyze_toclear.push(l);
                }
            }
        }
    }
#endif
    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

#if LBD_BASED_CLAUSE_DELETION
        if (c.learnt() && c.activity() > 2)
            c.activity() = lbd(c);
#else
        if (c.learnt())
            claBumpActivity(c);
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
#if BRANCHING_HEURISTIC == CHB
                last_conflict[var(q)] = conflicts;
#elif BRANCHING_HEURISTIC == VSIDS
                varBumpActivity(var(q));
#endif
                conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

#if ALMOST_CONFLICT
    seen[var(p)] = true;
    for(int i = out_learnt.size() - 1; i >= 0; i--) {
        Var v = var(out_learnt[i]);
        CRef rea = reason(v);
        if (rea != CRef_Undef) {
            Clause& reaC = ca[rea];
            for (int i = 0; i < reaC.size(); i++) {
                Lit l = reaC[i];
                if (!seen[var(l)]) {
                    seen[var(l)] = true;
                    almost_conflicted[var(l)]++;
                    analyze_toclear.push(l);
                }
            }
        }
    }
#endif
    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    picked[var(p)] = conflicts;
#if ANTI_EXPLORATION
    uint64_t age = conflicts - canceled[var(p)];
    if (age > 0) {
        double decay = pow(0.95, age);
        activity[var(p)] *= decay;
        if (order_heap.inHeap(var(p))) {
            order_heap.increase(var(p));
        }
    }
#endif
    conflicted[var(p)] = 0;
#if ALMOST_CONFLICT
    almost_conflicted[var(p)] = 0;
#endif
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

int min(int a, int b) {
    return a < b ? a : b;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
#if LBD_BASED_CLAUSE_DELETION
    vec<double>& activity;
    reduceDB_lt(ClauseAllocator& ca_,vec<double>& activity_) : ca(ca_), activity(activity_) {}
#else
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
#endif
    bool operator () (CRef x, CRef y) { 
#if LBD_BASED_CLAUSE_DELETION
        return ca[x].activity() > ca[y].activity();
    }
#else
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
#endif
};
void Solver::reduceDB()
{
    int     i, j;
#if LBD_BASED_CLAUSE_DELETION
    sort(learnts, reduceDB_lt(ca, activity));
#else
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity
    sort(learnts, reduceDB_lt(ca));
#endif

    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
#if LBD_BASED_CLAUSE_DELETION
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.activity() > 2 && !locked(c) && i < learnts.size() / 2)
#else
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
#endif
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    vec<Lit>    units;
    starts++;

    for (;;){
        CRef confl = propagate();

#if BRANCHING_HEURISTIC == CHB
        double multiplier = confl == CRef_Undef ? reward_multiplier : 1.0;
        for (int a = action; a < trail.size(); a++) {
            Var v = var(trail[a]);
            uint64_t age = conflicts - last_conflict[v] + 1;
            double reward = multiplier / age ;
            double old_activity = activity[v];
            activity[v] = step_size * reward + ((1 - step_size) * old_activity);
            if (order_heap.inHeap(v)) {
                if (activity[v] > old_activity)
                    order_heap.decrease(v);
                else
                    order_heap.increase(v);
            }
        }
#endif
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
#if BRANCHING_HEURISTIC == CHB || BRANCHING_HEURISTIC == LRB
            if (step_size > min_step_size)
                step_size -= step_size_dec;
#endif
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);

            cancelUntil(backtrack_level);

#if BRANCHING_HEURISTIC == CHB
            action = trail.size();
#endif

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
#if LBD_BASED_CLAUSE_DELETION
                Clause& clause = ca[cr];
                clause.activity() = lbd(clause);
#else
                claBumpActivity(ca[cr]);
#endif
                uncheckedEnqueue(learnt_clause[0], cr);
            }

#if BRANCHING_HEURISTIC == VSIDS
            varDecayActivity();
#endif
#if ! LBD_BASED_CLAUSE_DELETION
            claDecayActivity();
#endif

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
#if ! RAPID_DELETION
                max_learnts             *= learntsize_inc;
#endif

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (learnts.size()-nAssigns() >= max_learnts) {
                // Reduce the set of learnt clauses:
                reduceDB();
#if RAPID_DELETION
                max_learnts += 500;
#endif
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                callbackLearntClauses.clear();
                callbackFunction(next == lit_Undef, callbackLearntClauses);
                if (callbackLearntClauses.size() > 0) {
                    conflicts++; conflictC++;
                    int pending = learnts.size();
                    units.clear();
                    backtrack_level = decisionLevel();
                    for (int i = 0; i < callbackLearntClauses.size(); i++) {
                        #ifdef CHECK_LEARNED_CLAUSES_FOR_CONFLICT
                        int level = backtrack_level;
            			if(notInConflict(callbackLearntClauses[i]))
			            	callbackLearntClauses[i].copyTo(learnt_clause);
			            else
                        {	learnt_clause.clear();
                        	analyze(callbackLearntClauses[i], learnt_clause, level);
			            }
                        #else
                        int level;
                        learnt_clause.clear();
                        analyze(callbackLearntClauses[i], learnt_clause, level);
                        #endif
                        if (level == -1) {
                            return l_False;
                        } else if (level < backtrack_level) {
                            backtrack_level = level;
                        }
                        if (learnt_clause.size() == 1) {
                            units.push(learnt_clause[0]);
                        } else {
                            CRef cr = ca.alloc(learnt_clause, true);
                            learnts.push(cr);
                            attachClause(cr);
#if LBD_BASED_CLAUSE_DELETION
                            Clause& clause = ca[cr];
                            clause.activity() = lbd(clause);
#else
                            claBumpActivity(ca[cr]);
#endif
                        }
                    }

                    cancelUntil(backtrack_level);

#if BRANCHING_HEURISTIC == CHB
                    action = trail.size();
#endif

                    for (int i = 0; i < units.size(); i++) {
                        Lit l = units[i];
                        // Make sure it wasn't assigned by one of the other callback learnt clauses.
                        if (value(l) == l_Undef) uncheckedEnqueue(l);
                    }
                    for (int i = pending; i < learnts.size(); i++) {
                        CRef cr = learnts[i];
                        Clause& c = ca[cr];
                        bool asserting = assertingClause(cr);
                        if (asserting) uncheckedEnqueue(c[0], cr);
                    }
                    // Do not branch.
                    if (next != lit_Undef) {
                        insertVarOrder(var(next));
                        next = lit_Undef;
                    }
                } else if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            if (next != lit_Undef) {
                // Increase decision level and enqueue 'next'
                newDecisionLevel();
    #if BRANCHING_HEURISTIC == CHB
                action = trail.size();
    #endif
                uncheckedEnqueue(next);
            }
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

#if RAPID_DELETION
    max_learnts               = 2000;
#else
    max_learnts               = nClauses() * learntsize_factor;
#endif
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("LBD Based Clause Deletion : %d\n", LBD_BASED_CLAUSE_DELETION);
        printf("Rapid Deletion : %d\n", RAPID_DELETION);
        printf("Almost Conflict : %d\n", ALMOST_CONFLICT);
        printf("Anti Exploration : %d\n", ANTI_EXPLORATION);
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");

#ifdef FILTERING_STATS
    printf("A: %d\n", nconfs[0]);
    printf("B: %d\n", nconfs[1]);
    printf("C: %d\n", nconfs[2]);
    printf("D: %d\n", nconfs[3]);
    printf("AB: %d\n", ABconfs);
    printf("AC: %d\n", ACconfs);
    printf("AD: %d\n", ADconfs);
    printf("BC: %d\n", BCconfs);
    printf("BD: %d\n", BDconfs);
    printf("CD: %d\n", CDconfs);
    printf("ABC: %d\n", ABCconfs);
    printf("ABD: %d\n", ABDconfs);
    printf("ACD: %d\n", ACDconfs);
    printf("BCD: %d\n", BCDconfs);
    printf("ABCD: %d\n", ABCDconfs);
#endif

    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
