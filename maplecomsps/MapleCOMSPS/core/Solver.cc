/***************************************************************************************[Solver.cc]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

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

#include <math.h>
#include <signal.h>
#include <unistd.h>
#include <complex>

#include "mtl/Sort.h"
#include "core/Solver.h"

#include <sys/time.h>
typedef unsigned long long timestamp_t;

static timestamp_t
get_timestamp ()
{
  struct timeval now;
  gettimeofday (&now, NULL);
  return  now.tv_usec + (timestamp_t)now.tv_sec * 1000000;
}

int calls1 = 0;
int calls2 = 0;
int calls3 = 0;
int calls4 = 0;
int success1 = 0;
int success2 = 0;
int success3 = 0;
int success4 = 0;
double time1 = 0;
double time2 = 0;
double time3 = 0;
double time4 = 0;

using namespace Minisat;

#ifdef BIN_DRUP
int Solver::buf_len = 0;
unsigned char Solver::drup_buf[2 * 1024 * 1024];
unsigned char* Solver::buf_ptr = drup_buf;
#endif

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_step_size         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.80,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

static IntOption     opt_order     (_cat, "order",      "Order of matrix", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_carda     (_cat, "carda",      "Sum of real entries of A", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_cardb     (_cat, "cardb",      "Sum of imaginary entries of A", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_cardc     (_cat, "cardc",      "Sum of real entries of B", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_cardd     (_cat, "cardd",      "Sum of imaginary entries of B", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_numreala  (_cat, "numreala",   "Number of real entries of A", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_numrealb  (_cat, "numrealb",   "Number of real entries of B", -1, IntRange(-1, INT32_MAX));

static StringOption  opt_prodvars  (_cat, "prodvars",   "A file which contains a list of all product variables in the SAT instance.");

int** A;
int** B;

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    drup_file        (NULL)
  , verbosity        (0)
  , step_size        (opt_step_size)
  , step_size_dec    (opt_step_size_dec)
  , min_step_size    (opt_min_step_size)
  , timer            (5000)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , VSIDS            (false)
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
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), conflicts_VSIDS(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , order(opt_order)
  , carda (opt_carda)
  , cardb (opt_cardb)
  , cardc (opt_cardc)
  , cardd (opt_cardd)
  , numreala (opt_numreala)
  , numrealb (opt_numrealb)
  , prodvars (opt_prodvars)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches_bin        (WatcherDeleted(ca))
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap_CHB     (VarOrderLt(activity_CHB))
  , order_heap_VSIDS   (VarOrderLt(activity_VSIDS))
  , progress_estimate  (0)
  , remove_satisfied   (true)

  , core_lbd_cut       (3)
  , global_lbd_sum     (0)
  , lbd_queue          (50)
  , next_T2_reduce     (10000)
  , next_L_reduce      (15000)
  
  , counter            (0)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches_bin.init(mkLit(v, false));
    watches_bin.init(mkLit(v, true ));
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity_CHB  .push(0);
    activity_VSIDS.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);

    picked.push(0);
    conflicted.push(0);
    almost_conflicted.push(0);
#ifdef ANTI_EXPLORATION
    canceled.push(0);
#endif

    seen     .push(0);
    seen2    .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
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

    if (drup_file){
        add_oc.clear();
        for (int i = 0; i < ps.size(); i++) add_oc.push(ps[i]); }

    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (drup_file && i != j){
#ifdef BIN_DRUP
        binDRUP('a', ps, drup_file);
        binDRUP('d', add_oc, drup_file);
#else   
        for (int i = 0; i < ps.size(); i++)
            fprintf(drup_file, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
        fprintf(drup_file, "0\n");

        fprintf(drup_file, "d ");
        for (int i = 0; i < add_oc.size(); i++)
            fprintf(drup_file, "%i ", (var(add_oc[i]) + 1) * (-2 * sign(add_oc[i]) + 1));
        fprintf(drup_file, "0\n");
#endif
    }

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
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    ws[~c[0]].push(Watcher(cr, c[1]));
    ws[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    
    if (strict){
        remove(ws[~c[0]], Watcher(cr, c[1]));
        remove(ws[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        ws.smudge(~c[0]);
        ws.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];

    if (drup_file){
        if (c.mark() != 1){
#ifdef BIN_DRUP
            binDRUP('d', c, drup_file);
#else
            fprintf(drup_file, "d ");
            for (int i = 0; i < c.size(); i++)
                fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
            fprintf(drup_file, "0\n");
#endif
        }else
            printf("c Bug. I don't expect this to happen.\n");
    }

    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)){
        Lit implied = c.size() != 2 ? c[0] : (value(c[0]) == l_True ? c[0] : c[1]);
        vardata[var(implied)].reason = CRef_Undef; }
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

            if (!VSIDS){
                uint32_t age = conflicts - picked[x];
                if (age > 0){
                    double adjusted_reward = ((double) (conflicted[x] + almost_conflicted[x])) / ((double) age);
                    double old_activity = activity_CHB[x];
                    activity_CHB[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
                    if (order_heap_CHB.inHeap(x)){
                        if (activity_CHB[x] > old_activity)
                            order_heap_CHB.decrease(x);
                        else
                            order_heap_CHB.increase(x);
                    }
                }
#ifdef ANTI_EXPLORATION
                canceled[x] = conflicts;
#endif
            }

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
    Heap<VarOrderLt>& order_heap = VSIDS ? order_heap_VSIDS : order_heap_CHB;

    // Random decision:
    /*if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }*/

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty())
            return lit_Undef;
        else{
#ifdef ANTI_EXPLORATION
            if (!VSIDS){
                Var v = order_heap_CHB[0];
                uint32_t age = conflicts - canceled[v];
                while (age > 0){
                    double decay = pow(0.95, age);
                    activity_CHB[v] *= decay;
                    if (order_heap_CHB.inHeap(v))
                        order_heap_CHB.increase(v);
                    canceled[v] = conflicts;
                    v = order_heap_CHB[0];
                    age = conflicts - canceled[v];
                }
            }
#endif
            next = order_heap.removeMin();
        }

    return mkLit(next, polarity[next]);
}

/*_________________________________________________________________________________________________
|
|  analyze : (conflvec : vec<Lit>&) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
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
void Solver::analyze(vec<Lit>& conflvec, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int pathC = 0;
	CRef confl;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    int cur_max = level(var(conflvec[0]));
    for(int j=1; j < conflvec.size(); j++) {
           if(level(var(conflvec[j])) > cur_max) {
              cur_max = level(var(conflvec[j]));
           }
    }

    if(cur_max == 0)
    {   out_btlevel = -1;
        return;
    }

    /*// For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
    if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False){
        assert(value(c[1]) == l_True);
        Lit tmp = c[0];
        c[0] = c[1], c[1] = tmp; }

    // Update LBD if improved.
    if (c.learnt() && c.mark() != CORE){
        int lbd = computeLBD(c);
        if (lbd < c.lbd()){
            if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
            c.set_lbd(lbd);
            if (lbd <= core_lbd_cut){
                learnts_core.push(confl);
                c.mark(CORE);
            }else if (lbd <= 6 && c.mark() == LOCAL){
                // Bug: 'cr' may already be in 'learnts_tier2', e.g., if 'cr' was demoted from TIER2
                // to LOCAL previously and if that 'cr' is not cleaned from 'learnts_tier2' yet.
                learnts_tier2.push(confl);
                c.mark(TIER2); }
        }

        if (c.mark() == TIER2)
            c.touched() = conflicts;
        else if (c.mark() == LOCAL)
            claBumpActivity(c);
    }*/

    for (int j = (p == lit_Undef) ? 0 : 1; j < conflvec.size(); j++){
        Lit q = conflvec[j];

        if (!seen[var(q)] && level(var(q)) > 0){
            if (VSIDS){
                varBumpActivity(var(q), .5);
                add_tmp.push(q);
            }else
                conflicted[var(q)]++;
            seen[var(q)] = 1;
            if (level(var(q)) >= cur_max){
                pathC++;
            }else
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

        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        // Update LBD if improved.
        if (c.learnt() && c.mark() != CORE){
            int lbd = computeLBD(c);
            if (lbd < c.lbd()){
                if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd);
                if (lbd <= core_lbd_cut){
                    learnts_core.push(confl);
                    c.mark(CORE);
                }else if (lbd <= 6 && c.mark() == LOCAL){
                    // Bug: 'cr' may already be in 'learnts_tier2', e.g., if 'cr' was demoted from TIER2
                    // to LOCAL previously and if that 'cr' is not cleaned from 'learnts_tier2' yet.
                    learnts_tier2.push(confl);
                    c.mark(TIER2); }
            }

            if (c.mark() == TIER2)
                c.touched() = conflicts;
            else if (c.mark() == LOCAL)
                claBumpActivity(c);
        }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                if (VSIDS){
                    varBumpActivity(var(q), .5);
                    add_tmp.push(q);
                }else
                    conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= cur_max){
                    pathC++;
                }else
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
                for (int k = c.size() == 2 ? 0 : 1; k < c.size(); k++)
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

    out_lbd = computeLBD(out_learnt);
    if (out_lbd <= 6 && out_learnt.size() <= 30) // Try further minimization?
        if (binResMinimize(out_learnt))
            out_lbd = computeLBD(out_learnt); // Recompute LBD if minimized.

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

    if (VSIDS){
        for (int i = 0; i < add_tmp.size(); i++){
            Var v = var(add_tmp[i]);
            if (level(v) >= out_btlevel - 1)
                varBumpActivity(v, 1);
        }
        add_tmp.clear();
    }else{
        seen[var(p)] = true;
        for(int i = out_learnt.size() - 1; i >= 0; i--){
            Var v = var(out_learnt[i]);
            CRef rea = reason(v);
            if (rea != CRef_Undef){
                const Clause& reaC = ca[rea];
                for (int i = 0; i < reaC.size(); i++){
                    Lit l = reaC[i];
                    if (!seen[var(l)]){
                        seen[var(l)] = true;
                        almost_conflicted[var(l)]++;
                        analyze_toclear.push(l); } } } } }

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
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
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

        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        // Update LBD if improved.
        if (c.learnt() && c.mark() != CORE){
            int lbd = computeLBD(c);
            if (lbd < c.lbd()){
                if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd);
                if (lbd <= core_lbd_cut){
                    learnts_core.push(confl);
                    c.mark(CORE);
                }else if (lbd <= 6 && c.mark() == LOCAL){
                    // Bug: 'cr' may already be in 'learnts_tier2', e.g., if 'cr' was demoted from TIER2
                    // to LOCAL previously and if that 'cr' is not cleaned from 'learnts_tier2' yet.
                    learnts_tier2.push(confl);
                    c.mark(TIER2); }
            }

            if (c.mark() == TIER2)
                c.touched() = conflicts;
            else if (c.mark() == LOCAL)
                claBumpActivity(c);
        }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                if (VSIDS){
                    varBumpActivity(var(q), .5);
                    add_tmp.push(q);
                }else
                    conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()){
                    pathC++;
                }else
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
                for (int k = c.size() == 2 ? 0 : 1; k < c.size(); k++)
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

    out_lbd = computeLBD(out_learnt);
    if (out_lbd <= 6 && out_learnt.size() <= 30) // Try further minimization?
        if (binResMinimize(out_learnt))
            out_lbd = computeLBD(out_learnt); // Recompute LBD if minimized.

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

    if (VSIDS){
        for (int i = 0; i < add_tmp.size(); i++){
            Var v = var(add_tmp[i]);
            if (level(v) >= out_btlevel - 1)
                varBumpActivity(v, 1);
        }
        add_tmp.clear();
    }else{
        seen[var(p)] = true;
        for(int i = out_learnt.size() - 1; i >= 0; i--){
            Var v = var(out_learnt[i]);
            CRef rea = reason(v);
            if (rea != CRef_Undef){
                const Clause& reaC = ca[rea];
                for (int i = 0; i < reaC.size(); i++){
                    Lit l = reaC[i];
                    if (!seen[var(l)]){
                        seen[var(l)] = true;
                        almost_conflicted[var(l)]++;
                        analyze_toclear.push(l); } } } } }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Try further learnt clause minimization by means of binary clause resolution.
bool Solver::binResMinimize(vec<Lit>& out_learnt)
{
    // Preparation: remember which false variables we have in 'out_learnt'.
    counter++;
    for (int i = 1; i < out_learnt.size(); i++)
        seen2[var(out_learnt[i])] = counter;

    // Get the list of binary clauses containing 'out_learnt[0]'.
    const vec<Watcher>& ws = watches_bin[~out_learnt[0]];

    int to_remove = 0;
    for (int i = 0; i < ws.size(); i++){
        Lit the_other = ws[i].blocker;
        // Does 'the_other' appear negatively in 'out_learnt'?
        if (seen2[var(the_other)] == counter && value(the_other) == l_True){
            to_remove++;
            seen2[var(the_other)] = counter - 1; // Remember to remove this variable.
        }
    }

    // Shrink.
    if (to_remove > 0){
        int last = out_learnt.size() - 1;
        for (int i = 1; i < out_learnt.size() - to_remove; i++)
            if (seen2[var(out_learnt[i])] != counter)
                out_learnt[i--] = out_learnt[last--];
        out_learnt.shrink(to_remove);
    }
    return to_remove != 0;
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

        // Special handling for binary clauses like in 'analyze()'.
        if (c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

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
                for (int j = c.size() == 2 ? 0 : 1; j < c.size(); j++)
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
    Var x = var(p);
    if (!VSIDS){
        picked[x] = conflicts;
        conflicted[x] = 0;
        almost_conflicted[x] = 0;
#ifdef ANTI_EXPLORATION
        uint32_t age = conflicts - canceled[var(p)];
        if (age > 0){
            double decay = pow(0.95, age);
            activity_CHB[var(p)] *= decay;
            if (order_heap_CHB.inHeap(var(p)))
                order_heap_CHB.increase(var(p));
        }
#endif
    }

    assigns[x] = lbool(!sign(p));
    vardata[x] = mkVarData(from, decisionLevel());
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
    watches_bin.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        vec<Watcher>& ws_bin = watches_bin[p];  // Propagate binary clauses first.
        for (int k = 0; k < ws_bin.size(); k++){
            Lit the_other = ws_bin[k].blocker;
            if (value(the_other) == l_False){
                confl = ws_bin[k].cref;
#ifdef LOOSE_PROP_STAT
                return confl;
#else
                goto ExitProp;
#endif
            }else if(value(the_other) == l_Undef)
                uncheckedEnqueue(the_other, ws_bin[k].cref);
        }

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

ExitProp:;
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
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
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) const { return ca[x].activity() < ca[y].activity(); }
};
void Solver::reduceDB()
{
    int     i, j;
    //if (local_learnts_dirty) cleanLearnts(learnts_local, LOCAL);
    //local_learnts_dirty = false;

    sort(learnts_local, reduceDB_lt(ca));

    int limit = learnts_local.size() / 2;
    for (i = j = 0; i < learnts_local.size(); i++){
        Clause& c = ca[learnts_local[i]];
        if (c.mark() == LOCAL)
            if (c.removable() && !locked(c) && i < limit)
                removeClause(learnts_local[i]);
            else{
                if (!c.removable()) limit++;
                c.removable(true);
                learnts_local[j++] = learnts_local[i]; }
    }
    learnts_local.shrink(i - j);

    checkGarbage();
}
void Solver::reduceDB_Tier2()
{
    int i, j;
    for (i = j = 0; i < learnts_tier2.size(); i++){
        Clause& c = ca[learnts_tier2[i]];
        if (c.mark() == TIER2)
            if (!locked(c) && c.touched() + 30000 < conflicts){
                learnts_local.push(learnts_tier2[i]);
                c.mark(LOCAL);
                //c.removable(true);
                c.activity() = 0;
                claBumpActivity(c);
            }else
                learnts_tier2[j++] = learnts_tier2[i];
    }
    learnts_tier2.shrink(i - j);
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

void Solver::safeRemoveSatisfied(vec<CRef>& cs, unsigned valid_mark)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.mark() == valid_mark)
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

    order_heap_CHB  .build(vs);
    order_heap_VSIDS.build(vs);
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
    removeSatisfied(learnts_core); // Should clean core first.
    safeRemoveSatisfied(learnts_tier2, TIER2);
    safeRemoveSatisfied(learnts_local, LOCAL);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

std::complex<double> hall_eval(std::complex<double> seq[], int len,
			       std::complex<double> value)
{
  std::complex<double> result(0.0,0.0);
  for (int i = 0; i<len; ++i)
  {
    result += seq[i]*pow(value,i);
  }
  return result;
}

bool hall_check(std::complex<double> seq[], int len, int nchecks)
{
  double epsilon = 0.1;
  double theta;
  double v;
  std::complex<double> imagConst(0.0,1.0);
  for (int i = 0; i<nchecks; ++i)
  {
    theta = i*2*M_PI/nchecks;
    v = std::abs(hall_eval(seq,len,std::exp(theta*imagConst)));
    v*=v;
    if (v>2*len+epsilon)
      return false;
  }
  return true;
}

bool Solver::autocorrelation_check(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int i = 0, j = 0, var = 0;

#ifdef PRINTCONF
    std::complex<double> zero (0, 0);
    std::complex<double> one (1, 0);
    std::complex<double> neg_one (-1, 0);
    std::complex<double> imag_unit (0, 1);
    std::complex<double> neg_imag_unit (0, -1);
    std::complex<double> Ae[order], Be[order];

    printf("A assigns: ");
    for(i = 0; i<order*2; i+=2)
    {   if(assigns[i] == l_False && assigns[i+1] == l_False)
            printf("1 "), Ae[i/2].real(1), Ae[i/2].imag(0);
        else if(assigns[i] == l_False && assigns[i+1] == l_True)
            printf("-1 "), Ae[i/2].real(-1), Ae[i/2].imag(0);
        else if(assigns[i] == l_True && assigns[i+1] == l_False)
            printf("i "), Ae[i/2].real(0), Ae[i/2].imag(1);
        else if(assigns[i] == l_True && assigns[i+1] == l_True)
            printf("-i "), Ae[i/2].real(0), Ae[i/2].imag(-1);
        else if(assigns[i] == l_False)
            printf("R ");
        else if(assigns[i] == l_True)
            printf("I ");
        else
            printf("? ");
    }
    printf("\n");

    printf("A product assigns:\n");
    for(i=0; i<order; i++)
    { for(j=i+1; j<order; j++)
      { /*if(assigns[A[i][j]]==l_False)
          printf("F");
        else if(assigns[A[i][j]]==l_True)
          printf("T");
        else if(assigns[A[i][j]]==l_Undef)
          printf("?");
        if(assigns[A[i][j]+1]==l_False)
          printf("F");
        else if(assigns[A[i][j]+1]==l_True)
          printf("T");
        else if(assigns[A[i][j]+1]==l_Undef)
          printf("?");*/
        //printf("%d ", A[i][j]);
        int var = A[i][j];
        if(assigns[var] == l_False && assigns[var+1] == l_False)
        {   printf("1 ");
            assert(Ae[i]*Ae[j] == zero || Ae[i]*conj(Ae[j]) == one);
        }
        else if(assigns[var] == l_False && assigns[var+1] == l_True)
        {   printf("-1 ");
            assert(Ae[i]*Ae[j] == zero || Ae[i]*conj(Ae[j]) == neg_one);
        }
        else if(assigns[var] == l_True && assigns[var+1] == l_False)
        {   printf("i ");
            assert(Ae[i]*Ae[j] == zero || Ae[i]*conj(Ae[j]) == imag_unit);
        }
        else if(assigns[var] == l_True && assigns[var+1] == l_True)
        {   printf("-i ");
            assert(Ae[i]*Ae[j] == zero || Ae[i]*conj(Ae[j]) == neg_imag_unit);
        }
        else if(assigns[var] == l_False)
            printf("R ");
        else if(assigns[var] == l_True)
            printf("I ");
        else
            printf("? ");
      }
      printf("\n");
    }

    printf("B assigns: ");
    for(i = order*2; i<order*4; i+=2)
    {   if(assigns[i] == l_False && assigns[i+1] == l_False)
            printf("1 "), Be[(i-2*order)/2].real(1), Be[(i-2*order)/2].imag(0);
        else if(assigns[i] == l_False && assigns[i+1] == l_True)
            printf("-1 "), Be[(i-2*order)/2].real(-1), Be[(i-2*order)/2].imag(0);
        else if(assigns[i] == l_True && assigns[i+1] == l_False)
            printf("i "), Be[(i-2*order)/2].real(0), Be[(i-2*order)/2].imag(1);
        else if(assigns[i] == l_True && assigns[i+1] == l_True)
            printf("-i "), Be[(i-2*order)/2].real(0), Be[(i-2*order)/2].imag(-1);
        else if(assigns[i] == l_False)
            printf("R ");
        else if(assigns[i] == l_True)
            printf("I ");
        else
            printf("? ");
    }
    printf("\n");

    printf("B product assigns:\n");
    for(i=0; i<order; i++)
    { for(j=i+1; j<order; j++)
      { /*if(assigns[B[i][j]]==l_False)
          printf("F");
        else if(assigns[B[i][j]]==l_True)
          printf("T");
        else if(assigns[B[i][j]]==l_Undef)
          printf("?");
        if(assigns[B[i][j]+1]==l_False)
          printf("F");
        else if(assigns[B[i][j]+1]==l_True)
          printf("T");
        else if(assigns[B[i][j]+1]==l_Undef)
          printf("?");*/
        //printf("%d ", B[i][j]);
        int var = B[i][j];
        if(assigns[var] == l_False && assigns[var+1] == l_False)
        {   printf("1 ");
            assert(Be[i]*Be[j] == zero || Be[i]*conj(Be[j]) == one);
        }
        else if(assigns[var] == l_False && assigns[var+1] == l_True)
        {   printf("-1 ");
            assert(Be[i]*Be[j] == zero || Be[i]*conj(Be[j]) == neg_one);
        }
        else if(assigns[var] == l_True && assigns[var+1] == l_False)
        {   printf("i ");
            assert(Be[i]*Be[j] == zero || Be[i]*conj(Be[j]) == imag_unit);
        }
        else if(assigns[var] == l_True && assigns[var+1] == l_True)
        {   printf("-i ");
            assert(Be[i]*Be[j] == zero || Be[i]*conj(Be[j]) == neg_imag_unit);
        }
        else if(assigns[var] == l_False)
            printf("R ");
        else if(assigns[var] == l_True)
            printf("I ");
        else
            printf("? ");
      }
      printf("\n");
    }
#endif

    vec<Lit> conflict;

    for(j = 1; j < order; j++)
    {
        bool complete = true;
        int num_reals = 0;
        int num_imags = 0;
        int real_true_count = 0;
        int real_false_count = 0;
        int imag_true_count = 0;
        int imag_false_count = 0;

        for(i = 0; i < order-j; i++)
        {   for(int k = 0; k < 2; k++)
            {   if(k==0)
                    var = A[i][i+j];
                else
                    var = B[i][i+j];
                if(assigns[var] == l_Undef)
                {   complete = false;
                    break;
                }
                else if(assigns[var] == l_False)
                {   num_reals++;
                    if(assigns[var+1] == l_False)
                        real_false_count++;
                    else if(assigns[var+1] == l_True)
                        real_true_count++;
                }
                else if(assigns[var] == l_True)
                {   num_imags++;
                    if(assigns[var+1] == l_False)
                        imag_false_count++;
                    else if(assigns[var+1] == l_True)
                        imag_true_count++;
                }
            }
            if(complete == false)
              break;
        }
        if(complete == false)
          continue;

        if(num_reals % 2 != 0 || num_imags % 2 != 0)
        {
            for(i = 0; i < order-j; i++)
            {   for(int k = 0; k < 2; k++)
                {   if(k==0)
                        var = A[i][i+j];
                    else
                        var = B[i][i+j];

                    assert(assigns[var] != l_Undef);
                    if(assigns[var] == l_False)
                        conflict.push(mkLit(var, false));
                    else
                        conflict.push(mkLit(var, true));
                }
            }

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

            return true;
        }

        if(real_false_count > num_reals/2 || real_true_count > num_reals/2)
        {
            for(i = 0; i < order-j; i++)
            {   for(int k = 0; k < 2; k++)
                {   if(k==0)
                        var = A[i][i+j];
                    else
                        var = B[i][i+j];

                    assert(assigns[var] != l_Undef);
                    if(assigns[var] == l_False)
                        conflict.push(mkLit(var, false));
                    else
                        conflict.push(mkLit(var, true));

                    if(real_false_count > num_reals/2 && assigns[var+1] == l_False)
                        conflict.push(mkLit(var+1, false));
                    else if(real_true_count > num_reals/2 && assigns[var+1] == l_True)
                        conflict.push(mkLit(var+1, true));
                }
            }

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

            return true;
        }

        if(imag_false_count > num_imags/2 || imag_true_count > num_imags/2)
        {
            for(i = 0; i < order-j; i++)
            {   for(int k = 0; k < 2; k++)
                {   if(k==0)
                        var = A[i][i+j];
                    else
                        var = B[i][i+j];

                    assert(assigns[var] != l_Undef);
                    if(assigns[var] == l_False)
                        conflict.push(mkLit(var, false));
                    else
                        conflict.push(mkLit(var, true));

                    if(imag_false_count > num_imags/2 && assigns[var+1] == l_False)
                        conflict.push(mkLit(var+1, false));
                    else if(imag_true_count > num_imags/2 && assigns[var+1] == l_True)
                        conflict.push(mkLit(var+1, true));
                }
            }

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

            return true;
        }

    }

    return false;
}

bool Solver::cardinality_check(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    vec<Lit> conflict;
    int golay_dimension = order;
    int no_of_significant_vars = golay_dimension * 4;

    bool atype_complete = true;
    int num_reals = 0;
    int real_true_count = 0;
    int real_false_count = 0;
    int num_imags = 0;
    int imag_true_count = 0;
    int imag_false_count = 0;

#ifdef PRINTCONF
    int real_A = 0;
    int imag_A = 0;
    int real_B = 0;
    int imag_B = 0;
#endif

	for(int i=0; i<golay_dimension*2; i+=2)
    {   if(assigns[i] == l_Undef)
		{   atype_complete = false;
		    break;
		}
		else if(assigns[i] == l_False)
		{   num_reals++;
		    if(assigns[i+1] == l_False)
		        real_false_count++;
		    else if(assigns[i+1] == l_True)
		        real_true_count++;
		}
		else if(assigns[i] == l_True)
		{   num_imags++;
		    if(assigns[i+1] == l_False)
		        imag_false_count++;
		    else if(assigns[i+1] == l_True)
		        imag_true_count++;
		}
	}

	if(numreala != -1)
	{	num_reals = numreala;
		num_imags = order - num_reals;
	}

    if(atype_complete || numreala != -1)
    {   
        assert(num_reals + num_imags == golay_dimension);
        if((carda % 2 != num_reals % 2) || (cardb % 2 != num_imags % 2))
        {   if(numreala != -1)
                printf("ERROR!!\n");
            for (int i = 0; i<golay_dimension*2; i+=2)
            {
	            if(assigns[i] == l_False)
    	            conflict.push(mkLit(i,false));
        	    else
                    conflict.push(mkLit(i,true));
            }
#ifdef PRINTCONF
            printf("conflict: incorrect number of reals/imags in A\n");
        printf("A: ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
            printf("size %d\tconflict:", conflict.size());
            for(int i=0; i<conflict.size(); i++)
                printf(" %c%d (%d)", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1, level(var(conflict[i])));
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d (%d)", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1, level(var(out_learnt[i])));
            printf("\n");
#endif
            return true;
        }
        int num_real_falses = (carda+num_reals)/2;
        /*printf("carda: %d\n", carda);
        printf("num_reals: %d\n", num_reals);
        printf("real_false_count: %d\n", real_false_count);
        printf("num_real_falses: %d\n", num_real_falses);
        printf("real_true_count: %d\n", real_true_count);*/
        if(real_false_count > num_real_falses || real_true_count > num_reals - num_real_falses)
        {
            for (int i = 0; i<golay_dimension*2; i+=2)
            {   if(numreala == -1)
                {  if(assigns[i] == l_False)
                      conflict.push(mkLit(i,false));
                    else if(assigns[i] == l_True)
                      conflict.push(mkLit(i,true));
                }
                if(real_false_count > num_real_falses && assigns[i+1] == l_False)
                    conflict.push(mkLit(i+1,false));
                else if(real_true_count > num_reals - num_real_falses && assigns[i+1] == l_True)
                    conflict.push(mkLit(i+1,true));
            }
#ifdef PRINTCONF
            printf("conflict: incorrect number of real falses in A\n");
        printf("A: ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
            printf("size %d\tconflict:", conflict.size());
            for(int i=0; i<conflict.size(); i++)
                printf(" %c%d (%d)", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1, level(var(conflict[i])));
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d (%d)", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1, level(var(out_learnt[i])));
            printf("\n");
#endif
            return true;
        }
        int num_imag_falses = (cardb+num_imags)/2;
        if(imag_false_count > num_imag_falses || imag_true_count > num_imags - num_imag_falses)
        {
            for (int i = 0; i<golay_dimension*2; i+=2)
            {   if(numreala == -1)
                {  if(assigns[i] == l_False)
                     conflict.push(mkLit(i,false));
                   else if(assigns[i] == l_True)
                     conflict.push(mkLit(i,true));
                }
                if(imag_false_count > num_imag_falses && assigns[i+1] == l_False)
                    conflict.push(mkLit(i+1,false));
                else if(imag_true_count > num_imags - num_imag_falses && assigns[i+1] == l_True)
                    conflict.push(mkLit(i+1,true));
            }
#ifdef PRINTCONF
            printf("conflict: incorrect number of imag falses in A\n");
        printf("A: ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
            printf("size %d\tconflict:", conflict.size());
            for(int i=0; i<conflict.size(); i++)
                printf(" %c%d (%d)", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1, level(var(conflict[i])));
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d (%d)", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1, level(var(out_learnt[i])));
            printf("\n");
#endif
            return true;
        }
    }

#ifdef PRINTCONF
    real_A = -real_true_count + real_false_count;
    imag_A = -imag_true_count + imag_false_count;
#endif

    bool btype_complete = true;
    num_reals = 0;
    real_true_count = 0;
    real_false_count = 0;
    num_imags = 0;
    imag_true_count = 0;
    imag_false_count = 0;

    for(int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
    {   if(assigns[i] == l_Undef)
        {   btype_complete = false;
            break;
        }
        else if(assigns[i] == l_False)
        {   num_reals++;
            if(assigns[i+1] == l_False)
                real_false_count++;
            else if(assigns[i+1] == l_True)
                real_true_count++;
        }
        else if(assigns[i] == l_True)
        {   num_imags++;
            if(assigns[i+1] == l_False)
                imag_false_count++;
            else if(assigns[i+1] == l_True)
                imag_true_count++;
        }
    }

	if(numrealb != -1)
	{	num_reals = numrealb;
		num_imags = order - num_reals;
	}

    if(btype_complete || numrealb != -1)
    {
        assert(num_reals + num_imags == golay_dimension);
        if((cardc % 2 != num_reals % 2) || (cardd % 2 != num_imags % 2))
        {   if(numrealb != -1)
                printf("ERROR!!\n");
            for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
            {
	            if(assigns[i] == l_False)
    	            conflict.push(mkLit(i,false));
        	    else
                    conflict.push(mkLit(i,true));
            }
#ifdef PRINTCONF
            printf("conflict: incorrect number of reals/imags in B\n");
        printf("B: ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
            printf("size %d\tconflict:", conflict.size());
            for(int i=0; i<conflict.size(); i++)
                printf(" %c%d (%d)", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1, level(var(conflict[i])));
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d (%d)", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1, level(var(out_learnt[i])));
            printf("\n");
#endif
            return true;
        }
        int num_real_falses = (cardc+num_reals)/2;
        if(real_false_count > num_real_falses || real_true_count > num_reals - num_real_falses)
        {
            for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
            {   if(numrealb == -1)
                {   if(assigns[i] == l_False)
                      conflict.push(mkLit(i,false));
                    else if(assigns[i] == l_True)
                      conflict.push(mkLit(i,true));
                }
                if(real_true_count > num_reals - num_real_falses && assigns[i+1] == l_True)
                    conflict.push(mkLit(i+1,true));
                else if(real_false_count > num_real_falses && assigns[i+1] == l_False)
                    conflict.push(mkLit(i+1,false));
            }
#ifdef PRINTCONF
            printf("conflict: incorrect number of real falses in B\n");
        printf("B: ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
            printf("size %d\tconflict:", conflict.size());
            for(int i=0; i<conflict.size(); i++)
                printf(" %c%d (%d)", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1, level(var(conflict[i])));
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d (%d)", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1, level(var(out_learnt[i])));
            printf("\n");
#endif
            return true;
        }
        int num_imag_falses = (cardd+num_imags)/2;
        if(imag_false_count > num_imag_falses || imag_true_count > num_imags - num_imag_falses)
        {
            for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
            {   if(numrealb == -1)
                {   if(assigns[i] == l_False)
                      conflict.push(mkLit(i,false));
                    else if(assigns[i] == l_True)
                      conflict.push(mkLit(i,true));
                }
                if(imag_true_count > num_imags - num_imag_falses && assigns[i+1] == l_True)
                    conflict.push(mkLit(i+1,true));
                else if(imag_false_count > num_imag_falses && assigns[i+1] == l_False)
                    conflict.push(mkLit(i+1,false));
            }
#ifdef PRINTCONF
            printf("conflict: incorrect number of imag falses in B\n");
        printf("B: ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
            printf("size %d\tconflict:", conflict.size());
            for(int i=0; i<conflict.size(); i++)
                printf(" %c%d (%d)", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1, level(var(conflict[i])));
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d (%d)", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1, level(var(out_learnt[i])));
            printf("\n");
#endif
            return true;
        }
    }

#ifdef PRINTCONF
    real_B = -real_true_count + real_false_count;
    imag_B = -imag_true_count + imag_false_count;

    if(atype_complete && btype_complete)
    {   printf("%d %d %d %d\n", real_A, imag_A, real_B, imag_B);

        printf("A: ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i = 0; i<golay_dimension*2; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");

        printf("B: ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("1 ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("-1 ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("i ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("-i ");
            else if(assigns[i] == l_False)
                printf("R ");
            else if(assigns[i] == l_True)
                printf("I ");
        }
        printf("( ");
        for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
        {   if(assigns[i] == l_False && assigns[i+1] == l_False)
                printf("FF ");
            else if(assigns[i] == l_False && assigns[i+1] == l_True)
                printf("FT ");
            else if(assigns[i] == l_True && assigns[i+1] == l_False)
                printf("TF ");
            else if(assigns[i] == l_True && assigns[i+1] == l_True)
                printf("TT ");
            else if(assigns[i] == l_False)
                printf("F? ");
            else if(assigns[i] == l_True)
                printf("T? ");
        }
        printf(")\n");
    }
#endif

    return false;    
}

bool Solver::programmatic_check(vec<Lit>& out_learnt, int&
				out_btlevel, int& out_lbd)
{
  int golay_dimension = order;
  int no_of_significant_vars = golay_dimension * 4;
  std::complex<double> *a_fills =
    (std::complex<double>*)malloc(golay_dimension*sizeof(std::complex<double>));
  std::complex<double> *b_fills =
    (std::complex<double>*)malloc(golay_dimension*sizeof(std::complex<double>));
  bool a_complete = true;
  bool b_complete = true;
  for (int i = 0; i<golay_dimension*2; i+=2)
  {
    if (assigns[i]==l_Undef || assigns[i+1]==l_Undef)
    {
      a_complete = false;
      break;
    }
    if(assigns[i] == l_False && assigns[i+1] == l_False)
    {
      a_fills[i/2] = std::complex<double>(1,0);
    }
    if(assigns[i] == l_False && assigns[i+1] == l_True)
    {
      a_fills[i/2] = std::complex<double>(-1,0);
    }
    if(assigns[i] == l_True && assigns[i+1] == l_False)
    {
      a_fills[i/2] = std::complex<double>(0,1);
    }
    if(assigns[i] == l_True && assigns[i+1] == l_True)
    {
      a_fills[i/2] = std::complex<double>(0,-1);
    }
  }
  for (int i = golay_dimension*2;i<no_of_significant_vars; i+=2)
  {
    if (assigns[i]==l_Undef || assigns[i+1]==l_Undef)
    {
      b_complete = false;
      break;
    }
    if(assigns[i] == l_False && assigns[i+1] == l_False)
    {
      b_fills[(i-golay_dimension*2)/2] = std::complex<double>(1,0);
    }
    if(assigns[i] == l_False && assigns[i+1] == l_True)
    {
      b_fills[(i-golay_dimension*2)/2] = std::complex<double>(-1,0);
    }
    if(assigns[i] == l_True && assigns[i+1] == l_False)
    {
      b_fills[(i-golay_dimension*2)/2] = std::complex<double>(0,1);
    }
    if(assigns[i] == l_True && assigns[i+1] == l_True)
    {
      b_fills[(i-golay_dimension*2)/2] = std::complex<double>(0,-1);
    }
  }
  if (!a_complete && !b_complete)
  {
    free(a_fills);
    free(b_fills);
    return false;
  }

  vec<Lit> conflict;

  if (a_complete)
  {
    if (!hall_check(a_fills,golay_dimension,100))
    {
#ifdef PRINTCONF
      printf("conflict: filtering theorem for sequence A\n");
#endif
      for (int i = 0; i<golay_dimension*2; i++)
      {
	if(assigns[i] == l_False)
	  conflict.push(mkLit(i,false));
	else
	  conflict.push(mkLit(i,true));
      }
    }
  }
  else if (b_complete)
  {
#ifdef PRINTCONF
      printf("conflict: filtering theorem for sequence B\n");
#endif
    if (!hall_check(b_fills,golay_dimension,100))
    {
      for (int i = golay_dimension*2;i<no_of_significant_vars; i++)
      {
	if(assigns[i] == l_False)
	  conflict.push(mkLit(i,false));
	else
	  conflict.push(mkLit(i,true));
      }
    }
  }

#ifdef PRINTCONF
  printf("size %d\tconflict:", conflict.size());
  for(int i=0; i<conflict.size(); i++)
    printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
  printf("\n");
#endif
  
  if(conflict.size()==0)
    return false;

  out_learnt.clear();

  if(conflict.size()==1)
  { out_btlevel = 0;
    conflict.copyTo(out_learnt);
  }
  else
    analyze(conflict, out_learnt, out_btlevel, out_lbd);

#ifdef PRINTCONF
  printf("size %d\tout learnt:", out_learnt.size());
  for(int i=0; i<out_learnt.size(); i++)
    printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
  printf("\n");
#endif

  free(a_fills); free(b_fills);
  return true;
}

bool Solver::callback_function(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
	bool result1 = false;
	bool result2 = false;
	bool result3 = false;
	vec<Lit> out_learnt1;
	vec<Lit> out_learnt2;
	vec<Lit> out_learnt3;
	int out_btlevel1;
	int out_btlevel2;
	int out_btlevel3;
	int out_lbd1;
	int out_lbd2;
	int out_lbd3;

	if(carda != -1)
	{	
		calls2++;
		timestamp_t t0 = get_timestamp();
		if(cardinality_check(out_learnt2, out_btlevel2, out_lbd2))
			success2++, result2 = true;
		timestamp_t t1 = get_timestamp();
		time2 += (t1 - t0) / 1000000.0L;
	}

	if(result2)
	{
		out_learnt2.copyTo(out_learnt);
		out_btlevel = out_btlevel2;
		out_lbd = out_lbd2;
		return true;
	}

	if(order != -1)
	{
		calls1++;
		timestamp_t t0 = get_timestamp();
		if(programmatic_check(out_learnt1, out_btlevel1, out_lbd1))
			success1++, result1 = true;
		timestamp_t t1 = get_timestamp();
		time1 += (t1 - t0) / 1000000.0L;
	}

	if(result1)
	{
		out_learnt1.copyTo(out_learnt);
		out_btlevel = out_btlevel1;
		out_lbd = out_lbd1;
		return true;
	}

	if(prodvars != NULL)
	{
		calls3++;
		timestamp_t t0 = get_timestamp();
		if(autocorrelation_check(out_learnt3, out_btlevel3, out_lbd3))
			success3++, result3 = true;
		timestamp_t t1 = get_timestamp();
		time3 += (t1 - t0) / 1000000.0L;
	}
  
	if(result3)
	{
		out_learnt3.copyTo(out_learnt);
		out_btlevel = out_btlevel3;
		out_lbd = out_lbd3;
		return true;
	}

	return false;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int& nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         lbd;
    vec<Lit>    learnt_clause;
    bool        cached = false;
    starts++;

    for (;;){
        CRef confl = propagate();

        if (confl != CRef_Undef){
            // CONFLICT
            if (VSIDS){
                if (--timer == 0 && var_decay < 0.95) timer = 5000, var_decay += 0.01;
            }else
                if (step_size > min_step_size) step_size -= step_size_dec;

            conflicts++; nof_conflicts--;
            if (conflicts == 100000 && learnts_core.size() < 100) core_lbd_cut = 5;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, lbd);
            cancelUntil(backtrack_level);

            lbd--;
            if (VSIDS){
                cached = false;
                conflicts_VSIDS++;
                lbd_queue.push(lbd);
                global_lbd_sum += (lbd > 50 ? 50 : lbd);
            }

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                ca[cr].set_lbd(lbd);
                if (lbd <= core_lbd_cut){
                    learnts_core.push(cr);
                    ca[cr].mark(CORE);
                }else if (lbd <= 6){
                    learnts_tier2.push(cr);
                    ca[cr].mark(TIER2);
                    ca[cr].touched() = conflicts;
                }else{
                    learnts_local.push(cr);
                    claBumpActivity(ca[cr]); }
                attachClause(cr);
                uncheckedEnqueue(learnt_clause[0], cr);
            }
            if (drup_file){
#ifdef BIN_DRUP
                binDRUP('a', learnt_clause, drup_file);
#else
                for (int i = 0; i < learnt_clause.size(); i++)
                    fprintf(drup_file, "%i ", (var(learnt_clause[i]) + 1) * (-2 * sign(learnt_clause[i]) + 1));
                fprintf(drup_file, "0\n");
#endif
            }

            if (VSIDS) varDecayActivity();
            claDecayActivity();

            /*if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }*/

        }else{
            // NO CONFLICT
            bool restart = false;
            if (!VSIDS)
                restart = nof_conflicts <= 0;
            else if (!cached){
                restart = lbd_queue.full() && (lbd_queue.avg() * 0.8 > global_lbd_sum / conflicts_VSIDS);
                cached = true;
            }
            if (restart /*|| !withinBudget()*/){
                lbd_queue.clear();
                cached = false;
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (conflicts >= next_T2_reduce){
                next_T2_reduce = conflicts + 10000;
                reduceDB_Tier2(); }
            if (conflicts >= next_L_reduce){
                next_L_reduce = conflicts + 15000;
                reduceDB(); }

			learnt_clause.clear();

            if(callback_function(learnt_clause, backtrack_level, lbd)) {
				conflicts++; //conflictC++;
                if (decisionLevel() == 0 || backtrack_level == -1) return l_False;

                cancelUntil(backtrack_level);

				if (learnt_clause.size() == 1){
		            uncheckedEnqueue(learnt_clause[0]);
		        }else{
		            CRef cr = ca.alloc(learnt_clause, true);
		            ca[cr].set_lbd(lbd);
		            if (lbd <= core_lbd_cut){
		                learnts_core.push(cr);
		                ca[cr].mark(CORE);
		            }else if (lbd <= 6){
		                learnts_tier2.push(cr);
		                ca[cr].mark(TIER2);
		                ca[cr].touched() = conflicts;
		            }else{
		                learnts_local.push(cr);
		                claBumpActivity(ca[cr]); }
		            attachClause(cr);
		            uncheckedEnqueue(learnt_clause[0], cr);
		        }
			} else {
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

		            if (next == lit_Undef)
					{
						// Add call to python here
                        learnt_clause.clear();
                        if(callback_function(learnt_clause, backtrack_level, lbd)) {
							conflicts++; //conflictC++;
						    if (decisionLevel() == 0 || backtrack_level == -1) return l_False;

						    cancelUntil(backtrack_level);

							if (learnt_clause.size() == 1){
								uncheckedEnqueue(learnt_clause[0]);
							}else{
								CRef cr = ca.alloc(learnt_clause, true);
								ca[cr].set_lbd(lbd);
								if (lbd <= core_lbd_cut){
								    learnts_core.push(cr);
								    ca[cr].mark(CORE);
								}else if (lbd <= 6){
								    learnts_tier2.push(cr);
								    ca[cr].mark(TIER2);
								    ca[cr].touched() = conflicts;
								}else{
								    learnts_local.push(cr);
								    claBumpActivity(ca[cr]); }
								attachClause(cr);
								uncheckedEnqueue(learnt_clause[0], cr);
							}
						} else {
			                // Model found:
			                return l_True;
						}
					} else {
						// Increase decision level and enqueue 'next'
						newDecisionLevel();
						uncheckedEnqueue(next);
					}
		        } else {
				    // Increase decision level and enqueue 'next'
				    newDecisionLevel();
				    uncheckedEnqueue(next);
				}
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

static bool switch_mode = false;
static void SIGALRM_switch(int signum) { switch_mode = true; }

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    if(prodvars != NULL)
    {
        A = new int*[order];
        B = new int*[order];
        for(int i=0; i<order; i++)
        {
            A[i] = new int[order];
            B[i] = new int[order];
        }
 
        FILE* prodvar_file = fopen(prodvars, "r");
        if(prodvar_file == NULL)
          printf("ERROR! Could not open file: %s\n", prodvars), exit(1);

        char seq = '\0';
        int i = 0, j = 0, var = 0;
        while(fscanf(prodvar_file, "%c %d %d %d\n", &seq, &i, &j, &var) == 4)
        { //printf("%c %d %d %d\n", seq, i, j, var);
          if(seq == 'A')
          {
            A[i][j] = var-1;
          }
          else if(seq == 'B')
          {
            B[i][j] = var-1;
          }
          else
            printf("ERROR! Unknown seq type: %c\n", seq), exit(1);
        }

        fclose(prodvar_file);
    }

    signal(SIGALRM, SIGALRM_switch);
    alarm(2500);

    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("c ============================[ Search Statistics ]==============================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("c ===============================================================================\n");
    }

    add_tmp.clear();

    VSIDS = true;
    int init = 10000;
    while (status == l_Undef && init > 0 /*&& withinBudget()*/)
       status = search(init);
    VSIDS = false;

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef /*&& withinBudget()*/){
        if (VSIDS){
            int weighted = INT32_MAX;
            status = search(weighted);
        }else{
            int nof_conflicts = luby(restart_inc, curr_restarts) * restart_first;
            curr_restarts++;
            status = search(nof_conflicts);
        }
        if (!VSIDS && switch_mode){
            VSIDS = true;
            printf("c Switched to VSIDS.\n");
            fflush(stdout);
            picked.clear();
            conflicted.clear();
            almost_conflicted.clear();
#ifdef ANTI_EXPLORATION
            canceled.clear();
#endif
        }
    }

    if (verbosity >= 1)
        printf("c ===============================================================================\n");

#ifdef BIN_DRUP
    if (drup_file && status == l_False) binDRUP_flush(drup_file);
#endif

    if(prodvars != NULL)
    {
        for(int i=0; i<order; i++)
        {
            delete [] A[i];
            delete [] B[i];
        }
        delete [] A;
        delete [] B;
    }

    printf("filtering       checks: %d successes, %d total, %.2f total time\n", success1, calls1, time1);
    printf("cardinality     checks: %d successes, %d total, %.2f total time\n", success2, calls2, time2);
    printf("autocorrelation checks: %d successes, %d total, %.2f total time\n", success3, calls3, time3);

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
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watches_bin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws_bin = watches_bin[p];
            for (int j = 0; j < ws_bin.size(); j++)
                ca.reloc(ws_bin[j].cref, to);
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
    for (int i = 0; i < learnts_core.size(); i++)
        ca.reloc(learnts_core[i], to);
    for (int i = 0; i < learnts_tier2.size(); i++)
        ca.reloc(learnts_tier2[i], to);
    for (int i = 0; i < learnts_local.size(); i++)
        ca.reloc(learnts_local[i], to);

    // All original:
    //
    int i, j;
    for (i = j = 0; i < clauses.size(); i++)
        if (ca[clauses[i]].mark() != 1){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i]; }
    clauses.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
