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

#include <math.h>
#include <cstdio>
#include <complex>

#include "mtl/Sort.h"
#include "core/Solver.h"

//#define PRINTCONF

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_step_size         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_restart_xi (_cat, "restart-xi", "Initial step size for macd-short",  0.1,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_restart_discount_factor (_cat, "restart-discount-factor", "Restart discount factor",  0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_macd_short_step_size (_cat, "macd-short-step-size", "Initial step size for macd-short",  0.97,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_macd_long_step_size  (_cat, "macd-long-step-size",  "Initial step size for macd-long",   0.99,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_blocking_step_size   (_cat, "blocking-step-size",   "Initial step size for blocking",    0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static IntOption     opt_restart           (_cat, "restart",     "Controls the restart strategy (0=luby, 1=linear, 2=pow, 3=macd, 4=rl)", 4, IntRange(0, 4));
static DoubleOption  opt_restart_step_size (_cat, "restart-step-size", "Initial restart step size",               0.9,     DoubleRange(0, false, 1, false));
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static DoubleOption  opt_reward_multiplier (_cat, "reward-multiplier", "Reward multiplier", 0.9, DoubleRange(0, true, 1, true));

static IntOption     opt_order     (_cat, "order",      "Order of matrix", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_carda     (_cat, "carda",      "Cardinality of row A", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_cardb     (_cat, "cardb",      "Cardinality of row B", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_cardc     (_cat, "cardc",      "Cardinality of row C", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_cardd     (_cat, "cardd",      "Cardinality of row D", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_period    (_cat, "period",     "Period of programmatic check", 1, IntRange(1, INT32_MAX));

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , step_size        (opt_step_size)
  , step_size_dec    (opt_step_size_dec)
  , min_step_size    (opt_min_step_size)
  , restart_xi       (opt_restart_xi)
  , restart_discount_factor (opt_restart_discount_factor)
  , macd_short_step_size (opt_macd_short_step_size)
  , macd_long_step_size  (opt_macd_long_step_size)
  , blocking_step_size (opt_blocking_step_size)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , restart          (opt_restart)
  , restart_step_size(opt_restart_step_size)
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

  , lbds(0)
  , lbd_calls(0)
  , action(0)
  , reward_multiplier(opt_reward_multiplier)
  , order(opt_order)
  , carda (opt_carda)
  , cardb (opt_cardb)
  , cardc (opt_cardc)
  , cardd (opt_cardd)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
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
  , programmaticPeriod (opt_period)
{
    for (int i = 0; i < NUM_RESTART_TYPES; i++) {
        restart_activity[i] = 0;
        restart_ucb_X[i] = 0;
        restart_ucb_N[i] = 0;
    }
}


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
    conflicted.push(0);
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
        }else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}

restart_type Solver::pickRestart() {
    double max = -1;
    int index = -1;
    double n = 0;
    double B = 0;
    for (int i = 0; i < NUM_RESTART_TYPES; i++) {
        if (restart_ucb_N[i] == 0) {
            return (restart_type) i;
        }
        double X = restart_ucb_X[i] / restart_ucb_N[i];
        if (X > B) {
            B = X;
        }
        n += restart_ucb_N[i];
    }
    B = 1;
    double numerator = restart_xi * log(n);
    for (int i = 0; i < NUM_RESTART_TYPES; i++) {
        double X = restart_ucb_X[i] / restart_ucb_N[i];
        double c = 2 * B * sqrt(numerator / restart_ucb_N[i]);
        double activity = X + c;
        restart_activity[i] = activity;
        if (activity > max) {
            max = activity;
            index = i;
        }
    }
    if (index < 0) {
        printf("pickRestart: index = %d\n", index);
        exit(1);
    }
    return (restart_type) index;
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : vec<Lit>&) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
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

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    for (int j = (p == lit_Undef) ? 0 : 1; j < conflvec.size(); j++){
        Lit q = conflvec[j];

        /*if (!seen[var(q)] && level(var(q)) > 0){
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
        }*/
        if (!seen[var(q)] && level(var(q)) > 0){
            // varBumpActivity(var(q));
            // conflicted[var(q)]++;
            conflicted[var(q)] = conflicts;
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
    while (pathC > 0) {
        Clause& c = ca[confl];

#ifdef LBD_BASED_CLAUSE_DELETION
        if (c.learnt() && c.activity() > 2)
            c.activity() = lbd(c);
#else
        if (c.learnt())
            claBumpActivity(c);
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            /*if (!seen[var(q)] && level(var(q)) > 0){
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
            }*/
            if (!seen[var(q)] && level(var(q)) > 0){
                // varBumpActivity(var(q));
                // conflicted[var(q)]++;
                conflicted[var(q)] = conflicts;
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
	//printf("%d\n", confl);

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

#ifdef LBD_BASED_CLAUSE_DELETION
        if (c.learnt() && c.activity() > 2)
            c.activity() = lbd(c);
#else
        if (c.learnt())
            claBumpActivity(c);
#endif

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                // varBumpActivity(var(q));
                conflicted[var(q)] = conflicts;
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

#define PRINTCONF

bool Solver::cardinality_check(/*Lit isReal, Var start_var, Var end_var, int card,*/
                vec<Lit>& out_learnt, int& out_btlevel)
{   //return false;

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

    int real_A = 0;
    int imag_A = 0;
    int real_B = 0;
    int imag_B = 0;

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

    if(atype_complete)
    {   
        assert(num_reals + num_imags == golay_dimension);
        if((carda % 2 != num_reals % 2) || (cardb % 2 != num_imags % 2))
        {
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
                printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
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
            {
	            if(assigns[i] == l_False)
    	            conflict.push(mkLit(i,false));
        	    else
                    conflict.push(mkLit(i,true));
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
                printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
            printf("\n");
#endif
            return true;
        }
        int num_imag_falses = (cardb+num_imags)/2;
        if(imag_false_count > num_imag_falses || imag_true_count > num_imags - num_imag_falses)
        {
            for (int i = 0; i<golay_dimension*2; i+=2)
            {
	            if(assigns[i] == l_False)
    	            conflict.push(mkLit(i,false));
        	    else
                    conflict.push(mkLit(i,true));
                if(imag_false_count > num_imags && assigns[i+1] == l_False)
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
                printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
            printf("\n");
#endif
            return true;
        }
    }

    real_A = -real_true_count + real_false_count;
    imag_A = -imag_true_count + imag_false_count;

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

    if(btype_complete)
    {
        assert(num_reals + num_imags == golay_dimension);
        if((cardc % 2 != num_reals % 2) || (cardd % 2 != num_imags % 2))
        {
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
                printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
            printf("\n");
#endif
            return true;
        }
        int num_real_falses = (cardc+num_reals)/2;
        if(real_false_count > num_real_falses || real_true_count > num_reals - num_real_falses)
        {
            for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
            {
	            if(assigns[i] == l_False)
    	            conflict.push(mkLit(i,false));
        	    else
                    conflict.push(mkLit(i,true));
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
                printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
            printf("\n");
#endif
            return true;
        }
        int num_imag_falses = (cardd+num_imags)/2;
        if(imag_false_count > num_imag_falses || imag_true_count > num_imags - num_imag_falses)
        {
            for (int i=golay_dimension*2; i<no_of_significant_vars; i+=2)
            {
	            if(assigns[i] == l_False)
    	            conflict.push(mkLit(i,false));
        	    else
                    conflict.push(mkLit(i,true));
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
                printf(" %c%d", sign(conflict[i]) ? '-' : '+', var(conflict[i])+1);
            printf("\n");
#endif

            out_learnt.clear();
            analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
            printf("size %d\tout learnt:", out_learnt.size());
            for(int i=0; i<out_learnt.size(); i++)
                printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
            printf("\n");
#endif
            return true;
        }
    }

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

    return false;    
}

bool Solver::programmatic_check(vec<Lit>& out_learnt, int&
				out_btlevel)
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
    analyze(conflict, out_learnt, out_btlevel);

#ifdef PRINTCONF
  printf("size %d\tout learnt:", out_learnt.size());
  for(int i=0; i<out_learnt.size(); i++)
    printf(" %c%d", sign(out_learnt[i]) ? '-' : '+', var(out_learnt[i])+1);
  printf("\n");
#endif

  free(a_fills); free(b_fills);
  return true;
}

bool Solver::callback_function(vec<Lit>& out_learnt, int& out_btlevel)
{

  programmaticCount++;
  bool result = false;
  if(programmaticCount >= programmaticPeriod)
  {  programmaticCount = 0;
     if(programmatic_check(out_learnt, out_btlevel))
     {
       result = true;
     }
     else if(carda != -1 && cardb != -1 && cardc != -1 && cardd != -1 && cardinality_check(out_learnt, out_btlevel))
     { 
        /*if(carda == 1 and cardb == 1 and cardc == 1 and cardd == 3 and order == 6)
        {
           char* onesol = "FFTFFFFTFTFFTTTFTFTFFFTF";
           bool at_least_one_true = false;
           for(int i=0; i<out_learnt.size(); i++)
           {    if(sign(out_learnt[i]) && onesol[var(out_learnt[i])] == 'T')
                    at_least_one_true = true;
                else if(!sign(out_learnt[i]) && onesol[var(out_learnt[i])] == 'F')
                    at_least_one_true = true;
           }
           if(!at_least_one_true)
           {    printf("CONFLICT CLAUSE PROBLEM\n");
                exit(0);
           }
        }*/

        result = true;
     }
  }
  return result;
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
#ifdef LBD_BASED_CLAUSE_DELETION
    vec<double>& activity;
    reduceDB_lt(ClauseAllocator& ca_,vec<double>& activity_) : ca(ca_), activity(activity_) {}
#else
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
#endif
    bool operator () (CRef x, CRef y) { 
#ifdef LBD_BASED_CLAUSE_DELETION
        return ca[x].activity() > ca[y].activity();
    }
#else
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
#endif
};
void Solver::reduceDB()
{
    int     i, j;
#ifdef LBD_BASED_CLAUSE_DELETION
    sort(learnts, reduceDB_lt(ca, activity));
#else
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity
    sort(learnts, reduceDB_lt(ca));
#endif

    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
#ifdef LBD_BASED_CLAUSE_DELETION
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

void Solver::updateQ(Var v, double multiplier) {
    uint64_t age = conflicts - conflicted[v] + 1;
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
    starts++;

    double macd_short = 0;
    double macd_long = 0;
    double blocking_long = 0;
    for (;;){
        CRef confl = propagate();

        for (int a = action; a < trail.size(); a++) {
            Var v = var(trail[a]);
            updateQ(v, confl == CRef_Undef ? reward_multiplier : 1.0);
        }
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (step_size > min_step_size)
                step_size -= step_size_dec;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);

            cancelUntil(backtrack_level);

            action = trail.size();

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
#ifdef LBD_BASED_CLAUSE_DELETION
                Clause& clause = ca[cr];
                int l = lbd(clause);
                if (conflictC == 1) {
                    macd_short = l;
                    macd_long = l;
                    blocking_long = nAssigns();
                } else {
                    macd_short = macd_short_step_size * macd_short + (1.0 - macd_short_step_size) * l;
                    macd_long = macd_long_step_size * macd_long + (1.0 - macd_long_step_size) * l;
                    blocking_long = blocking_step_size * blocking_long + (1.0 - blocking_step_size) * nAssigns();
                }
                clause.activity() = l;
                lbds += l;
#else
                claBumpActivity(ca[cr]);
#endif
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            //varDecayActivity();
#ifndef LBD_BASED_CLAUSE_DELETION
            claDecayActivity();
#endif

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                //max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts ||  nof_conflicts < 0 && conflictC > 50 && macd_short > 1.15 * macd_long && blocking_long * 1.4 > nAssigns() || !withinBudget()){
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
                max_learnts += 500;
            }

            /*Lit next = lit_Undef;
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
            }*/
            learnt_clause.clear();

            if(callback_function(learnt_clause, backtrack_level)) {
                conflicts++; conflictC++;
                if (decisionLevel() == 0) return l_False;

                cancelUntil(backtrack_level);

                if(learnt_clause.size() == 1)
                    uncheckedEnqueue(learnt_clause[0]);
                else {
                    CRef cr = ca.alloc(learnt_clause, true);
                    learnts.push(cr);
#ifdef LBD_BASED_CLAUSE_DELETION
                    Clause& clause = ca[cr];
                    int l = lbd(clause);
                    if (conflictC == 1) {
                        macd_short = l;
                        macd_long = l;
                        blocking_long = nAssigns();
                    } else {
                        macd_short = macd_short_step_size * macd_short + (1.0 - macd_short_step_size) * l;
                        macd_long = macd_long_step_size * macd_long + (1.0 - macd_long_step_size) * l;
                        blocking_long = blocking_step_size * blocking_long + (1.0 - blocking_step_size) * nAssigns();
                    }
                    clause.activity() = l;
                    lbds += l;
#else
                    claBumpActivity(ca[cr]);
#endif
                    attachClause(cr);
                    uncheckedEnqueue(learnt_clause[0], cr);
                }
            } else {
                Lit next = lit_Undef;
                while (decisionLevel() < assumptions.size()) {
                    // Perform user provided assumption:
                    Lit p = assumptions[decisionLevel()];
                    if (value(p) == l_True){
                        // Dummy decision level:
                        newDecisionLevel();
                    } else if (value(p) == l_False) {
                        analyzeFinal(~p, conflict);
                        return l_False;
                    } else {
                        next = p;
                        break;
                    }
                }

                if (next == lit_Undef) {
                    // New variable decision:
                    decisions++;
                    next = pickBranchLit();

                    if (next == lit_Undef) {
                        // Add call to python here
                        learnt_clause.clear();
                        programmaticCount = programmaticPeriod;
                        
                        if(callback_function(learnt_clause, backtrack_level)) {
                            conflicts++; conflictC++;
                            if (decisionLevel() == 0) return l_False;

                            cancelUntil(backtrack_level);

                            if(learnt_clause.size() == 1)
                                uncheckedEnqueue(learnt_clause[0]);
                            else {
                                CRef cr = ca.alloc(learnt_clause, true);
                                learnts.push(cr);
#ifdef LBD_BASED_CLAUSE_DELETION
                                Clause& clause = ca[cr];
                                int l = lbd(clause);
                                if (conflictC == 1) {
                                    macd_short = l;
                                    macd_long = l;
                                    blocking_long = nAssigns();
                                } else {
                                    macd_short = macd_short_step_size * macd_short + (1.0 - macd_short_step_size) * l;
                                    macd_long = macd_long_step_size * macd_long + (1.0 - macd_long_step_size) * l;
                                    blocking_long = blocking_step_size * blocking_long + (1.0 - blocking_step_size) * nAssigns();
                                }
                                clause.activity() = l;
                                lbds += l;
#else
                                claBumpActivity(ca[cr]);
#endif
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
#if BRANCHING_HEURISTIC == CHB
                    action = trail.size();
#endif
                    uncheckedEnqueue(next);
                    }

                } else {
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

    max_learnts               = 2000;//nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int luby_restarts = 0;
    int linear_restarts = 0;
    int pow_restarts = 0;
    int macd_restarts = 0;
    while (status == l_Undef){
        double rest_base;
        restart_type r = pickRestart();
        printf("Using restart strategy: %d, activity[%f, %f, %f, %f]\n", r, restart_activity[0], restart_activity[1], restart_activity[2], restart_activity[3]);
        switch (r) {
            case LUBY:
                rest_base = luby(restart_inc, luby_restarts);
                luby_restarts++;
                break;
            case LINEAR:
                rest_base = linear_restarts + 1;
                linear_restarts++;
                break;
            case POW:
                rest_base = pow(restart_inc, pow_restarts);
                pow_restarts++;
                break;
            default:
                rest_base = 1;
                macd_restarts++;
                break;
        }

        lbds = 0;
        int nof_conflicts = rest_base * restart_first;
        uint64_t start_conflicts = conflicts;
        status = search(nof_conflicts);
        if (!withinBudget()) break;
        //printf("Restarted after %lu conflicts\n", conflicts - start_conflicts);
        double restart_reward = (double) ((long double) (conflicts - start_conflicts)) / ((long double) lbds);

        for (int i = 0; i < NUM_RESTART_TYPES; i++) {
            if (i == r) {
                restart_ucb_X[i] = restart_discount_factor * restart_ucb_X[i] + restart_reward;
                restart_ucb_N[i] = restart_discount_factor * restart_ucb_N[i] + 1.0;
            } else {
                restart_ucb_X[i] = restart_discount_factor * restart_ucb_X[i];
                restart_ucb_N[i] = restart_discount_factor * restart_ucb_N[i];
            }
        }
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


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
