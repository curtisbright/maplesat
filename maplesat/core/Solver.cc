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

#include "automorphisms.h"

#define MAXN 66

//#include "nauty.h"
#include "naututil.h"

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"

FILE* exhaustfile = NULL;
FILE* exhaustfile2 = NULL;
//FILE* transfile = NULL;

using namespace Minisat;

/*#include <set>
#include <vector>
std::set<std::vector<int>> transset;*/

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
static StringOption  opt_exhaustive(_cat, "exhaustive", "Output for exhaustive search");
static StringOption  opt_exhaustive2(_cat, "exhaustive2", "Output for exhaustive search2");
//static StringOption  opt_transfile(_cat, "transfile", "File for transitive blocking clauses");
static IntOption  opt_colmin(_cat, "colmin", "Minimum column to use for exhaustive search", -1);
static IntOption  opt_colmax(_cat, "colmax", "Maximum column to use for exhaustive search", -1);
static IntOption  opt_rowmin(_cat, "rowmin", "Minimum row to use for exhaustive search", -1);
static IntOption  opt_rowmax(_cat, "rowmax", "Maximum row to use for exhaustive search", -1);
//static IntOption  opt_colprint(_cat, "colprint", "Maximum column to use for printing", 111);
static BoolOption opt_isoblock(_cat, "isoblock", "Use isomorphism blocking", true);
//static BoolOption opt_isoblock2(_cat, "isoblock2", "Use isomorphism blocking2", false);
static BoolOption opt_eager(_cat, "eager", "Learn programmatic clauses eagerly", false);
static BoolOption opt_addunits(_cat, "addunits", "Add unit clauses to fix variables that do not appear in instance", false);
//static BoolOption opt_transblock(_cat, "transblock", "Use transitive blocking", false);
//static BoolOption opt_transread(_cat, "transread", "Read transitive blocking clauses", false);
static BoolOption opt_printtags(_cat, "printtags", "Print tags for isomorphism classes", false);


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
  , addunits           (opt_addunits)

  , exhauststring (opt_exhaustive)
  , exhauststring2 (opt_exhaustive2)
  //, transstring (opt_transfile)
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
    if(exhauststring2 != NULL)
    {   exhaustfile2 = fopen(exhauststring2, "a");
    }
    /*if(transstring != NULL && opt_transblock)
    {   transfile = fopen(transstring, "a");
    }*/
	/*if(transstring != NULL && opt_transread)
	{	transfile = fopen(transstring, "r");
		std::vector<int> clause;
		int i;
		fscanf(transfile, "%d", &i);    
		while(!feof(transfile))
	    	{	if(i!=0)
			{	clause.push_back(abs(i)-1);
			}
			else
			{	transset.insert(clause);
				clause.clear();
			}
			fscanf(transfile, "%d", &i);      
		}
		fclose(transfile);
	}*/
}


Solver::~Solver()
{
    if(exhauststring != NULL)
    {   fclose(exhaustfile);
    }
    if(exhauststring2 != NULL)
    {   fclose(exhaustfile2);
    }
    /*if(transfile != NULL)
    {   fclose(transfile);
    }*/
}


//=================================================================================================
// Minor methods:

void Solver::addLexClauses()
{
	for(int k=1; k<768; k++)
	{
		for(int i=30; i<66; i++)
		{	for(int j=13; j<21; j++)
			{	const int a1 = 111*i+j;
				const int a2 = 111*row[k][i]+col[k][j];
				if(i==30 && j==13)
				{	Var v = newVar();
					addClause(~mkLit(a1), mkLit(a2));
					addClause(~mkLit(a1), mkLit(v));
					addClause(mkLit(a2), mkLit(v));
				}
				else if(!(i==65 && j==20))
				{	Var v1 = nVars()-1;
					Var v2 = newVar();
					addClause(~mkLit(a1), mkLit(a2), ~mkLit(v1));
					addClause(~mkLit(a1), mkLit(v2), ~mkLit(v1));
					addClause(mkLit(a2), mkLit(v2), ~mkLit(v1));
				}
				else
				{	Var v = nVars()-1;
					addClause(~mkLit(a1), mkLit(a2), ~mkLit(v));
				}
			}
		}
	}
}


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

#include <array>
#include <set>

graph g[MAXN*MAXM];
graph canong[MAXN*MAXM];
int lab[MAXN],ptn[MAXN],orbits[MAXN];
DEFAULTOPTIONS_GRAPH(options);
statsblk stats;

long glist[10000];

//#include <algorithm>
//#include <utility>

//vec<Lit> blocking_clause;

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
	
	if(exhaustfile==NULL)
		return;

	/*bool all_assigned = true;
	for(int i=0; i<assigns.size(); i++)
	{	//printf("%c", assigns[i]==l_True ? '1' : (assigns[i]==l_False ? '0' : '?'));
		if(assigns[i]==l_Undef)
		{	all_assigned = false;
			break;
		}
	}
	//printf("\n");*/

	if(opt_eager && opt_rowmin != -1 && opt_rowmax != -1 && opt_colmin != -1 && opt_colmax != -1)
	{	
		for(int r=opt_rowmin; r<opt_rowmax; r++)
		{	for(int c=opt_colmin; c<opt_colmax; c++)
			{	const int index = 111*r+c;
				if(assigns[index]==l_Undef)
					return;
			}
		}
		/*if(!complete)
		{	printf("The following variables were not set: ");
			for(int i=0; i<assigns.size(); i++)
				if(assigns[i]==l_Undef)
					printf("%d ", i);
			printf("\n");
			exit(1);
		}*/
		complete = true;
	}

	if(complete)
	{
		vec<Lit> clause;
		out_learnts.push();
		
		/*fprintf(exhaustfile, "a ");
		for(int i=0; i<assigns.size(); i++)
		{	
			int r = (i/111);
			int c = (i%111);
			if(assigns[i]==l_True && r >= opt_rowmin && r < opt_rowmax && c >= opt_colmin && c < opt_colmax)
			{	clause.push(mkLit(i, assigns[i]==l_True));
				//out_learnts[0].push(mkLit(i, assigns[i]==l_True));
				fprintf(exhaustfile, "%s%d ", assigns[i]==l_True ? "" : "-", i+1);
			}
		}
		fprintf(exhaustfile, "0\n");*/

		for(int r=opt_rowmin; r<opt_rowmax; r++)
		{	for(int c=opt_colmin; c<opt_colmax; c++)
			{
				const int index = 111*r+c;
				if(assigns[index]==l_True)
				{	out_learnts[0].push(~mkLit(index));
					//fprintf(exhaustfile, "%d ", index+1);
				}
			}
		}
		//if(!opt_printtags)
		//	fprintf(exhaustfile, "0\n");
		//else
		//	fprintf(exhaustfile, "0 %d\n", numsols+1);

		/*
		{
			int max_index = 0;
			for(int i=1; i<out_learnts[0].size(); i++)
				if(level(var(out_learnts[0][i])) > level(var(out_learnts[0][max_index])))
					max_index = i;
			Lit p = out_learnts[0][0];
			out_learnts[0][0] = out_learnts[0][max_index];
			out_learnts[0][max_index] = p;
		}

		{
			int max_index = 1;
			for(int i=2; i<out_learnts[0].size(); i++)
				if(level(var(out_learnts[0][i])) > level(var(out_learnts[0][max_index])))
					max_index = i;
			Lit p = out_learnts[0][1];
			out_learnts[0][1] = out_learnts[0][max_index];
			out_learnts[0][max_index] = p;
		}

		CRef confl_clause = ca.alloc(out_learnts[0], false);
		attachClause(confl_clause);
		clauses.push(confl_clause);
		*/

		const int m = SETWORDSNEEDED(MAXN);
		const int n = MAXN;

		EMPTYGRAPH(g,m,n);

		for(int c=0; c<21; c++)
		{	for(int r1=0; r1<66; r1++)
			{	for(int r2=r1+1; r2<66; r2++)
				{
					const int index1 = 111*r1+c;
					const int index2 = 111*r2+c;
					if(assigns[index1]==l_True && assigns[index2]==l_True)
					{	ADDONEEDGE(g,r1,r2,m);
					}
				}
			}
		}

		//printf("%d\n", sizeof(graph));

		//putgraph(stdout, g, 0, m, n);

		options.writeautoms = FALSE;
		options.defaultptn = TRUE;
		options.writemarkers = FALSE;
		options.getcanon = TRUE;
		options.outfile=NULL;

		//nauty_check(WORDSIZE,m,n,NAUTYVERSIONID);

		densenauty(g,lab,ptn,orbits,&options,&stats,m,n,canong);

		/*printf("in");
		putgraph(stdout, g, 0, m, n);
		printf("out");
		putgraph(stdout, canong, 0, m, n);*/

		long hash = hashgraph(canong, m, n, 19883109L);

		bool found = true;
		for(int k=0; k<numsols; k++)
		{	//if(memcmp(&canong, &(glist[k]), sizeof(graph)*MAXN*MAXM)==0)
			if(hash==glist[k])
			{	found = false;
				//printf("Already found!\n");
				break;
			}
		}

		if(found)
		{	//memcpy(&(glist[numsols]), &canong, sizeof(graph)*MAXN*MAXM);
			glist[numsols] = hash;
			numsols++;

			fprintf(exhaustfile, "a ");

			for(int i=0; i<assumptions.size(); i++)
			{	out_learnts[0].push(~assumptions[i]);
				if(sign(assumptions[i]))
				{	
					//out_learnts[0].push(mkLit(var(assumptions[i])));
					//if(opt_printneg)
					fprintf(exhaustfile, "-%d ", var(assumptions[i])+1);
				}
				else
				{	
					//out_learnts[0].push(~mkLit(var(assumptions[i])));
					fprintf(exhaustfile, "%d ", var(assumptions[i])+1);
				}
			}

			for(int r=opt_rowmin; r<opt_rowmax; r++)
			{	for(int c=opt_colmin; c<opt_colmax; c++)
				{
					const int index = 111*r+c;
					if(assigns[index]==l_True)
					{	
						fprintf(exhaustfile, "%d ", index+1);
					}
				}
			}
			fprintf(exhaustfile, "0\n");
		}

		if(opt_isoblock)
		{
			std::array<std::array<int, 8>, 36> matrix;
			std::set<std::array<std::array<int, 8>, 36>> matrixset;
			for(int i=0; i<36; i++)
				for(int j=0; j<8; j++)
					matrix[i][j] = (assigns[111*(i+30)+(j+13)]==l_True?1:0);
			matrixset.insert(matrix);

			for(int k=0; k<768; k++)
			{
				if(k != identity_index)
				{
					for(int r=30; r<66; r++)
					{	for(int c=13; c<21; c++)
						{
							const int index = 111*r+c;
							if(assigns[index]==l_True)
								matrix[row[k][r]-30][col[k][c]-13] = 1;
							else
								matrix[row[k][r]-30][col[k][c]-13] = 0;
							
						}
					}

					//std::sort(matrix.begin(), matrix.end(), std::greater<>()); 
					/*for(int i=0; i<6; i++)
					{	for(int j=0; j<6; j++)
						{	if(matrix[j][15+i]==1)
								swap(matrix[i], matrix[j]);
						}

					}*/

					if(matrixset.count(matrix)>0)
						continue;

					matrixset.insert(matrix);

					//if(k == identity_index)
					//	printf("error!\n");

					//vec<Lit> clause;
					const int len = out_learnts.size();
					out_learnts.push();

					for(int i=0; i<36; i++)
						for(int j=0; j<8; j++)
							if(matrix[i][j]==1)
								//clause.push(~mkLit((i+30)*111+(j+13)));
								out_learnts[len].push(~mkLit((i+30)*111+(j+13)));
					/*
					{
						{
							int max_index = 0;
							for(int i=1; i<clause.size(); i++)
								if(level(var(clause[i])) > level(var(clause[max_index])))
									max_index = i;
							Lit p = clause[0];
							clause[0] = clause[max_index];
							clause[max_index] = p;
						}

						{
							int max_index = 1;
							for(int i=2; i<clause.size(); i++)
								if(level(var(clause[i])) > level(var(clause[max_index])))
									max_index = i;
							Lit p = clause[1];
							clause[1] = clause[max_index];
							clause[max_index] = p;
						}

						CRef confl_clause = ca.alloc(clause, false);
						attachClause(confl_clause);
						clauses.push(confl_clause);
					}
					*/

					/*
					if(exhaustfile2 != NULL && opt_printtags)
					{	fprintf(exhaustfile2, "a ");
						for(int r=0; r<66; r++)
						{	for(int c=0; c<21; c++)
							{	if(c>=12 && r>= 30)
									continue;
								const int index = 111*r+c;
								if(assigns[index]==l_True)
								{	fprintf(exhaustfile2, "%d ", index+1);
								}
							}
						}
					}

					for(int i=0; i<36; i++)
					{	
						for(int j=0; j<9; j++)
						{	if(matrix[i][j]==1)
							{	
								if(exhaustfile2 != NULL)
								{	if(opt_printtags)
									{	fprintf(exhaustfile2, "%d ", (i+30)*111+(j+12)+1);
									}
									else
									{	fprintf(exhaustfile2, "-%d ", (i+30)*111+(j+12)+1);
									}
								}
							}
						}
					}
					if(exhaustfile2 != NULL)
					{	fprintf(exhaustfile2, "0\n");
					}*/

				}
			}
		}

		/*if(opt_isoblock2)
		{

			for(int k=0; k<16; k++)
			{
				std::array<std::array<int, 75>, 6> matrix;
				std::array<std::array<int, 75>, 6> matrix2;

				if(row2[k]==1)
				{
					for(int r=21; r<27; r++)
					{	for(int c=0; c<75; c++)
						{
							const int index = 111*r+c;
							if(assigns[index]==l_True)
								matrix[r-21][col2[k][c]] = 1;
							else
								matrix[r-21][col2[k][c]] = 0;
							
						}
					}

					for(int i=0; i<6; i++)
					{	for(int j=0; j<6; j++)
						{	if(matrix[j][15+i]==1)
								swap(matrix[i], matrix[j]);
						}

					}

					for(int r=27; r<33; r++)
					{	for(int c=0; c<75; c++)
						{
							const int index = 111*r+c;
							if(assigns[index]==l_True)
								matrix2[r-27][col2[k][c]] = 1;
							else
								matrix2[r-27][col2[k][c]] = 0;
							
						}
					}

					for(int i=0; i<6; i++)
					{	for(int j=0; j<6; j++)
						{	if(matrix2[j][15+6+i]==1)
								swap(matrix2[i], matrix2[j]);
						}

					}

					vec<Lit> clause;

					for(int i=0; i<6; i++)
					{	for(int j=0; j<75; j++)
						{	if(matrix[i][j]==1)
							{	clause.push(~mkLit((i+21)*111+j));
							}
							if(matrix2[i][j]==1)
							{	clause.push(~mkLit((i+27)*111+j));
							}
						}
					}

					{
						int max_index = 0;
						for(int i=1; i<clause.size(); i++)
							if(level(var(clause[i])) > level(var(clause[max_index])))
								max_index = i;
						Lit p = clause[0];
						clause[0] = clause[max_index];
						clause[max_index] = p;
					}

					{
						int max_index = 1;
						for(int i=2; i<clause.size(); i++)
							if(level(var(clause[i])) > level(var(clause[max_index])))
								max_index = i;
						Lit p = clause[1];
						clause[1] = clause[max_index];
						clause[max_index] = p;
					}

					CRef confl_clause = ca.alloc(clause, false);
					attachClause(confl_clause);
					clauses.push(confl_clause);

				}
				if(row2[k]==10)
				{
					for(int r=27; r<33; r++)
					{	for(int c=0; c<75; c++)
						{
							const int index = 111*r+c;
							if(assigns[index]==l_True)
								matrix[r-27][col2[k][c]] = 1;
							else
								matrix[r-27][col2[k][c]] = 0;
							
						}
					}

					for(int i=0; i<6; i++)
					{	for(int j=0; j<6; j++)
						{	if(matrix[j][15+6+i]==1)
								swap(matrix[i], matrix[j]);
						}

					}

					for(int r=21; r<27; r++)
					{	for(int c=0; c<75; c++)
						{
							const int index = 111*r+c;
							if(assigns[index]==l_True)
								matrix2[r-21][col2[k][c]] = 1;
							else
								matrix2[r-21][col2[k][c]] = 0;
							
						}
					}

					for(int i=0; i<6; i++)
					{	for(int j=0; j<6; j++)
						{	if(matrix2[j][15+i]==1)
								swap(matrix2[i], matrix2[j]);
						}

					}

					vec<Lit> clause;

					for(int i=0; i<6; i++)
					{	for(int j=0; j<75; j++)
						{	if(matrix[i][j]==1)
							{	clause.push(~mkLit((i+21)*111+j));
							}
							if(matrix2[i][j]==1)
							{	clause.push(~mkLit((i+27)*111+j));
							}
						}
					}

					{
						int max_index = 0;
						for(int i=1; i<clause.size(); i++)
							if(level(var(clause[i])) > level(var(clause[max_index])))
								max_index = i;
						Lit p = clause[0];
						clause[0] = clause[max_index];
						clause[max_index] = p;
					}

					{
						int max_index = 1;
						for(int i=2; i<clause.size(); i++)
							if(level(var(clause[i])) > level(var(clause[max_index])))
								max_index = i;
						Lit p = clause[1];
						clause[1] = clause[max_index];
						clause[max_index] = p;
					}

					CRef confl_clause = ca.alloc(clause, false);
					attachClause(confl_clause);
					clauses.push(confl_clause);

				}
			}
		}*/
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

const int firstReduceDB = 2000;
const int incReduceDB = 300;
const int specialIncReduceDB = 1000;
long curRestart = 1;
int nbclausesbeforereduce = firstReduceDB;

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

  // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
  if(ca[learnts[learnts.size() / 2]].activity()<=3) {nbclausesbeforereduce +=specialIncReduceDB;}
  // Useless :-)
  if(ca[learnts.last()].activity()<=5)  {nbclausesbeforereduce +=specialIncReduceDB;}

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
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %8d |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), numsols /*progressEstimate()*100*/);
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

	    // Perform clause database reduction !
	    if(conflicts >=  curRestart * nbclausesbeforereduce )
	      {
		assert(learnts.size()>0);
		curRestart = (conflicts/ nbclausesbeforereduce)+1;
                reduceDB();
		nbclausesbeforereduce += incReduceDB;
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
                    cancelUntil(0);
                    //addClause_(conflict);
                    nbclausesbeforereduce = firstReduceDB;
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
                        int level;
                        learnt_clause.clear();
                        analyze(callbackLearntClauses[i], learnt_clause, level);
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
        /*printf("LBD Based Clause Deletion : %d\n", LBD_BASED_CLAUSE_DELETION);
        printf("Rapid Deletion : %d\n", RAPID_DELETION);
        printf("Almost Conflict : %d\n", ALMOST_CONFLICT);
        printf("Anti Exploration : %d\n", ANTI_EXPLORATION);*/
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Num Sols |\n");
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
    {   printf("===============================================================================\n");
        printf("Number of solutions: %ld\n", numsols);
    }

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
