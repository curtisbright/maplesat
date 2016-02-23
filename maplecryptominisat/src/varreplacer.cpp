/*
 * CryptoMiniSat
 *
 * Copyright (c) 2009-2015, Mate Soos. All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation
 * version 2.0 of the License.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
*/

#include "varreplacer.h"
#include "varupdatehelper.h"
#include "solver.h"
#include "clausecleaner.h"
#include "time_mem.h"
#include "solutionextender.h"
#include "clauseallocator.h"
#include "sqlstats.h"
#include "sccfinder.h"
#include <iostream>
#include <iomanip>
#include <set>
using std::cout;
using std::endl;

#ifdef VERBOSE_DEBUG
#define REPLACE_STATISTICS
#define VERBOSE_DEBUG_BIN_REPLACER
#endif

using namespace CMSat;

//#define VERBOSE_DEBUG
//#define REPLACE_STATISTICS
//#define DEBUG_BIN_REPLACER
//#define VERBOSE_DEBUG_BIN_REPLACER

VarReplacer::VarReplacer(Solver* _solver) :
    solver(_solver)
{
    scc_finder = new SCCFinder(_solver);
    ps_tmp.resize(2);
}

VarReplacer::~VarReplacer()
{
    delete scc_finder;
}

void VarReplacer::new_var(const Var orig_outer)
{
    if (orig_outer == std::numeric_limits<Var>::max()) {
        table.push_back(Lit(table.size(), false));
    }
}

void VarReplacer::check_no_replaced_var_set() const
{
    for(Var var = 0; var < solver->nVarsOuter(); var++) {
        if (solver->value(var) != l_Undef) {
            if (solver->varData[var].removed != Removed::none)
            {
                cout << "ERROR: var " << var + 1 << " has removed: "
                << removed_type_to_string(solver->varData[var].removed)
                << " but is set to " << solver->value(var) << endl;
                assert(solver->varData[var].removed == Removed::none);
                exit(-1);
            }
        }
    }
}

void VarReplacer::new_vars(const size_t n)
{
    size_t oldsize = table.size();
    table.resize(table.size()+n, lit_Undef);
    for(size_t i = oldsize; i < table.size(); i++) {
        table[i] = Lit(i, false);
    }
}

void VarReplacer::save_on_var_memory()
{
}

void VarReplacer::updateVars(
    const std::vector< uint32_t >& /*outerToInter*/
    , const std::vector< uint32_t >& /*interToOuter*/
) {

    /*updateArray(table, interToOuter);
    updateLitsMap(table, outerToInter);
    map<Var, vector<Var> > newReverseTable;
    for(map<Var, vector<Var> >::iterator
        it = reverseTable.begin(), end = reverseTable.end()
        ; it != end
        ; ++it
    ) {
        updateArrayMapCopy(it->second, outerToInter);
        newReverseTable[outerToInter.at(it->first)] = it->second;
    }
    reverseTable.swap(newReverseTable);*/
}

void VarReplacer::printReplaceStats() const
{
    uint32_t i = 0;
    for (vector<Lit>::const_iterator
        it = table.begin(); it != table.end()
        ; ++it, i++
    ) {
        if (it->var() == i) continue;
        cout << "Replacing var " << i+1 << " with Lit " << *it << endl;
    }
}

void VarReplacer::update_vardata_and_activities(
    const Var orig
    , const Var replaced_with
) {
    //Not replaced_with, or not replaceable, so skip
    if (orig == replaced_with
        || solver->varData[replaced_with].removed == Removed::decomposed
        || solver->varData[replaced_with].removed == Removed::elimed
    ) {
        return;
    }

    //Has already been handled previously, just skip
    if (solver->varData[orig].removed == Removed::replaced) {
        return;
    }

    //Okay, so unset decision, and set the other one decision
    assert(orig != replaced_with);
    solver->varData[orig].removed = Removed::replaced;
    assert(solver->varData[replaced_with].removed == Removed::none);
    assert(solver->value(replaced_with) == l_Undef);

    solver->set_decision_var(replaced_with);
    solver->unset_decision_var(orig);
    //solver->move_activity_from_to(orig, replaced_with);
}

bool VarReplacer::enqueueDelayedEnqueue()
{
    for(Lit lit: delayedEnqueue) {
        lit = get_lit_replaced_with(lit);
        if (solver->value(lit) == l_Undef) {
            solver->enqueue(lit);
            #ifdef STATS_NEEDED
            solver->propStats.propsUnit++;
            #endif
        } else if (solver->value(lit) == l_False) {
            solver->ok = false;
            break;
        }
    }
    delayedEnqueue.clear();

    if (!solver->ok)
        return false;

    solver->ok = solver->propagate<false>().isNULL();
    return solver->ok;
}

void VarReplacer::attach_delayed_attach()
{
    for(Clause* c: delayed_attach_or_free) {
        if (c->size() <= 3) {
            solver->cl_alloc.clauseFree(c);
        } else {
            if (c->red() && solver->red_long_cls_is_reducedb(*c)) {
                solver->num_red_cls_reducedb--;
            }
            c->unset_removed();
            solver->attachClause(*c);
        }
    }
    delayed_attach_or_free.clear();
}

void VarReplacer::update_all_vardata_activities()
{
    Var var = 0;
    for (vector<Lit>::const_iterator
        it = table.begin(); it != table.end()
        ; ++it, var++
    ) {
        const Var orig = solver->map_outer_to_inter(var);
        const Var repl = solver->map_outer_to_inter(it->var());
        update_vardata_and_activities(orig, repl);
    }
}

bool VarReplacer::perform_replace()
{
    assert(solver->ok);
    checkUnsetSanity();

    //Set up stats
    runStats.clear();
    runStats.numCalls = 1;
    const double myTime = cpuTime();
    const size_t origTrailSize = solver->trail_size();

    solver->clauseCleaner->remove_and_clean_all();
    solver->test_all_clause_attached();

    //Printing stats
    if (solver->conf.verbosity >= 5)
        printReplaceStats();

    update_all_vardata_activities();
    check_no_replaced_var_set();

    runStats.actuallyReplacedVars = replacedVars -lastReplacedVars;
    lastReplacedVars = replacedVars;

    solver->test_all_clause_attached();
    assert(solver->prop_at_head());

    #ifdef DEBUG_IMPLICIT_STATS
    solver->check_implicit_stats();
    #endif
    build_fast_inter_replace_lookup();

    //Replace implicits
    if (!replaceImplicit()) {
        goto end;
    }
    solver->watches.clear_smudged();

    //Replace longs
    assert(delayed_attach_or_free.empty());
    if (!replace_set(solver->longIrredCls)) {
        goto end;
    }
    if (!replace_set(solver->longRedCls)) {
        goto end;
    }
    solver->clean_occur_from_removed_clauses_only_smudged();
    attach_delayed_attach();

    //While replacing the clauses
    //we cannot(for implicits) and/or shouldn't (for implicit & long cls) enqueue
    //* We cannot because we are going through a struct and we might change it
    //* We shouldn't because then non-dominators would end up in the 'trail'
    if (!enqueueDelayedEnqueue()) {
        goto end;
    }

    solver->update_assumptions_after_varreplace();

end:
    delayed_attach_or_free.clear();
    destroy_fast_inter_replace_lookup();
    assert(solver->prop_at_head() || !solver->ok);

    //Update stats
    const double time_used = cpuTime() - myTime;
    runStats.zeroDepthAssigns += solver->trail_size() - origTrailSize;
    runStats.cpu_time = time_used;
    globalStats += runStats;
    if (solver->conf.verbosity  >= 1) {
        if (solver->conf.verbosity  >= 3)
            runStats.print(solver->nVars());
        else
            runStats.print_short(solver);
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "vrep"
            , time_used
        );
    }

    if (solver->okay()) {
        solver->test_all_clause_attached();
        solver->check_wrong_attach();
        #ifdef DEBUG_IMPLICIT_STATS
        solver->check_stats();
        #endif
        checkUnsetSanity();
    }

    return solver->ok;
}

void VarReplacer::newBinClause(
    Lit origLit1
    , Lit origLit2
    , Lit origLit3
    , Lit lit1
    , Lit lit2
    , bool red
) {
    //Only attach once
    if (origLit1 < origLit2
        && origLit2 < origLit3
    ){
        delayed_attach_bin.push_back(BinaryClause(lit1, lit2, red));
        (*solver->drup) << lit1 << lit2 << fin;
    }
}

void VarReplacer::updateTri(
    watch_subarray::iterator& i
    , watch_subarray::iterator& j
    , const Lit origLit1
    , const Lit origLit2
    , Lit lit1
    , Lit lit2
) {
    Lit lit3 = i->lit3();
    Lit origLit3 = lit3;
    assert(origLit1.var() != origLit3.var());
    assert(origLit2.var() != origLit3.var());
    assert(origLit2 < origLit3);
    assert(solver->value(origLit3) == l_Undef);

    //Update lit3
    if (get_lit_replaced_with_fast(lit3) != lit3) {
        lit3 = get_lit_replaced_with_fast(lit3);
        i->setLit3(lit3);
        runStats.replacedLits++;
    }

    bool remove = false;

    //Tautology, remove
    if (lit1 == ~lit2
        || lit1 == ~lit3
        || lit2 == ~lit3
    ) {
        remove = true;
    }

    //All 3 lits are the same
    if (!remove
        && lit1 == lit2
        && lit2 == lit3
    ) {
        delayedEnqueue.push_back(lit1);
        (*solver->drup) << lit1 << fin;
        remove = true;
    }

    //1st and 2nd lits are the same
    if (!remove
        && lit1 == lit2
    ) {
        newBinClause(origLit1, origLit2, origLit3, lit1, lit3, i->red());
        remove = true;
    }

    //1st and 3rd lits  OR 2nd and 3rd lits are the same
    if (!remove
        && (lit1 == lit3 || (lit2 == lit3))
    ) {
        newBinClause(origLit1, origLit2, origLit3, lit1, lit2, i->red());
        remove = true;
    }

    if (remove) {
        impl_tmp_stats.remove(*i);

        //Drup -- Only delete once
        if (origLit1 < origLit2
            && origLit2 < origLit3
        ) {
            (*solver->drup)
            << del
            << origLit1
            << origLit2
            << origLit3
            << fin;
        }

        return;
    }

    //Order literals
    orderLits(lit1, lit2, lit3);

    //Now make into the order this TRI was in
    if (origLit1 > origLit2
        && origLit1 < origLit3
    ) {
        std::swap(lit1, lit2);
    }
    if (origLit1 > origLit2
        && origLit1 > origLit3
    ) {
        std::swap(lit1, lit3);
        std::swap(lit2, lit3);
    }
    i->setLit2(lit2);
    i->setLit3(lit3);

    //Drup
    if (//Changed
        (lit1 != origLit1
            || lit2 != origLit2
            || lit3 != origLit3
        )
        //Remove&attach only once
        && (origLit1 < origLit2
            && origLit2 < origLit3
        )
    ) {
        (*solver->drup)
        << lit1 << lit2 << lit3 << fin
        << del << origLit1 << origLit2  << origLit3 << fin;
    }

    if (lit1 != origLit1) {
        solver->watches[lit1.toInt()].push(*i);
    } else {
        *j++ = *i;
    }

    return;
}

void VarReplacer::updateBin(
    watch_subarray::iterator& i
    , watch_subarray::iterator& j
    , const Lit origLit1
    , const Lit origLit2
    , Lit lit1
    , Lit lit2
) {
    bool remove = false;

    //Two lits are the same in BIN
    if (lit1 == lit2) {
        delayedEnqueue.push_back(lit2);
        (*solver->drup) << lit2 << fin;
        remove = true;
    }

    //Tautology
    if (lit1 == ~lit2)
        remove = true;

    if (remove) {
        impl_tmp_stats.remove(*i);

        //Drup -- Delete only once
        if (origLit1 < origLit2) {
            (*solver->drup) << del << origLit1 << origLit2 << fin;
        }

        return;
    }

    //Drup
    if (//Changed
        (lit1 != origLit1
            || lit2 != origLit2)
        //Delete&attach only once
        && (origLit1 < origLit2)
    ) {
        (*solver->drup)
        << lit1 << lit2 << fin
        << del << origLit1 << origLit2 << fin;
    }

    if (lit1 != origLit1) {
        solver->watches[lit1.toInt()].push(*i);
    } else {
        *j++ = *i;
    }
}

void VarReplacer::updateStatsFromImplStats()
{
    assert(impl_tmp_stats.removedRedBin % 2 == 0);
    solver->binTri.redBins -= impl_tmp_stats.removedRedBin/2;

    assert(impl_tmp_stats.removedIrredBin % 2 == 0);
    solver->binTri.irredBins -= impl_tmp_stats.removedIrredBin/2;

    assert(impl_tmp_stats.removedRedTri % 3 == 0);
    solver->binTri.redTris -= impl_tmp_stats.removedRedTri/3;

    assert(impl_tmp_stats.removedIrredTri % 3 == 0);
    solver->binTri.irredTris -= impl_tmp_stats.removedIrredTri/3;

    #ifdef DEBUG_IMPLICIT_STATS
    solver->check_implicit_stats();
    #endif

    runStats.removedBinClauses += impl_tmp_stats.removedRedBin/2 + impl_tmp_stats.removedIrredBin/2;
    runStats.removedTriClauses += impl_tmp_stats.removedRedTri/3 + impl_tmp_stats.removedIrredTri/3;

    impl_tmp_stats.clear();
}

bool VarReplacer::replaceImplicit()
{
    impl_tmp_stats.clear();
    delayedEnqueue.clear();
    delayed_attach_bin.clear();

    for(size_t i = 0; i < solver->nVars()*2; i++) {
        const Lit lit = Lit::toLit(i);
        if (get_lit_replaced_with_fast(lit) != lit) {
            solver->watches.smudge(lit);
        }
    }

    for(size_t at = 0; at < solver->watches.get_smudged_list().size(); at++) {
        const Lit origLit1 = solver->watches.get_smudged_list()[at];
        //const Lit origLit1 = Lit::toLit(at);
        watch_subarray ws = solver->watches[origLit1.toInt()];

        watch_subarray::iterator i = ws.begin();
        watch_subarray::iterator j = i;
        for (watch_subarray::iterator end2 = ws.end(); i != end2; i++) {
            //Don't bother clauses
            if (i->isClause()) {
                *j++ = *i;
                continue;
            }
            runStats.bogoprops += 1;

            const Lit origLit2 = i->lit2();
            assert(solver->value(origLit1) == l_Undef);
            assert(solver->value(origLit2) == l_Undef);
            assert(origLit1.var() != origLit2.var());

            //Update main lit
            Lit lit1 = origLit1;
            if (get_lit_replaced_with_fast(lit1) != lit1) {
                lit1 = get_lit_replaced_with_fast(lit1);
                runStats.replacedLits++;
                solver->watches.smudge(origLit2);
                if (i->isTri()) {
                    solver->watches.smudge(i->lit3());
                }
            }

            //Update lit2
            Lit lit2 = origLit2;
            if (get_lit_replaced_with_fast(lit2) != lit2) {
                lit2 = get_lit_replaced_with_fast(lit2);
                i->setLit2(lit2);
                runStats.replacedLits++;
            }

            if (i->isTri()) {
                updateTri(i, j, origLit1, origLit2, lit1, lit2);
            } else {
                assert(i->isBinary());
                updateBin(i, j, origLit1, origLit2, lit1, lit2);
            }
        }
        ws.shrink_(i-j);
    }

    for(const BinaryClause& bincl : delayed_attach_bin) {
        solver->attach_bin_clause(bincl.getLit1(), bincl.getLit2(), bincl.isRed());
    }
    delayed_attach_bin.clear();

    #ifdef VERBOSE_DEBUG_BIN_REPLACER
    cout << "c debug bin replacer start" << endl;
    cout << "c debug bin replacer end" << endl;
    #endif

    updateStatsFromImplStats();

    return solver->ok;
}

/**
@brief Replaces variables in long clauses
*/
bool VarReplacer::replace_set(vector<ClOffset>& cs)
{
    assert(!solver->drup->something_delayed());
    vector<ClOffset>::iterator i = cs.begin();
    vector<ClOffset>::iterator j = i;
    for (vector<ClOffset>::iterator end = cs.end(); i != end; i++) {
        runStats.bogoprops += 3;
        assert(!solver->drup->something_delayed());

        Clause& c = *solver->cl_alloc.ptr(*i);
        assert(!c.getRemoved());
        assert(c.size() > 3);

        bool changed = false;
        (*solver->drup) << deldelay << c << fin;

        const Lit origLit1 = c[0];
        const Lit origLit2 = c[1];

        for (Lit& l: c) {
            if (isReplaced_fast(l)) {
                changed = true;
                l = get_lit_replaced_with_fast(l);
                runStats.replacedLits++;
            }
        }

        if (changed && handleUpdatedClause(c, origLit1, origLit2)) {
            if (c.red() && solver->red_long_cls_is_reducedb(c)) {
                solver->num_red_cls_reducedb--;
            }
            runStats.removedLongClauses++;
            if (!solver->ok) {
                return false;
            }
        } else {
            *j++ = *i;
            solver->drup->forget_delay();
        }

    }
    cs.resize(cs.size() - (i-j));
    assert(!solver->drup->something_delayed());

    return solver->ok;
}

Lit* my_lit_find(Clause& cl, const Lit lit)
{
    for(Lit* a = cl.begin(); a != cl.end(); a++) {
        if (*a == lit)
            return a;
    }
    return NULL;
}

/**
@brief Helper function for replace_set()
*/
bool VarReplacer::handleUpdatedClause(
    Clause& c
    , const Lit origLit1
    , const Lit origLit2
) {
    assert(!c.getRemoved());
    bool satisfied = false;
    std::sort(c.begin(), c.end());
    Lit p;
    uint32_t i, j;
    const uint32_t origSize = c.size();
    for (i = j = 0, p = lit_Undef; i != origSize; i++) {
        assert(solver->varData[c[i].var()].removed == Removed::none);
        if (solver->value(c[i]) == l_True || c[i] == ~p) {
            satisfied = true;
            break;
        }
        else if (solver->value(c[i]) != l_False && c[i] != p) {
            c[j++] = p = c[i];
        }
    }
    c.shrink(i - j);
    c.setStrenghtened();

    runStats.bogoprops += 10;
    if (c.red()) {
        solver->litStats.redLits -= origSize;
    } else {
        solver->litStats.irredLits -= origSize;
    }
    delayed_attach_or_free.push_back(&c);

    #ifdef VERBOSE_DEBUG
    cout << "clause after replacing: " << c << endl;
    #endif

    if (satisfied) {
        (*solver->drup) << findelay;
        c.shrink(c.size()); //so we free() it
        solver->watches.smudge(origLit1);
        solver->watches.smudge(origLit2);
        c.setRemoved();
        return true;
    }
    (*solver->drup) << c << fin << findelay;

    runStats.bogoprops += 3;
    switch(c.size()) {
    case 0:
        c.setRemoved();
        solver->ok = false;
        return true;
    case 1 :
        c.setRemoved();
        solver->watches.smudge(origLit1);
        solver->watches.smudge(origLit2);

        delayedEnqueue.push_back(c[0]);
        runStats.removedLongLits += origSize;
        return true;
    case 2:
        c.setRemoved();
        solver->watches.smudge(origLit1);
        solver->watches.smudge(origLit2);

        solver->attach_bin_clause(c[0], c[1], c.red());
        runStats.removedLongLits += origSize;
        return true;

    case 3:
        c.setRemoved();
        solver->watches.smudge(origLit1);
        solver->watches.smudge(origLit2);

        solver->attach_tri_clause(c[0], c[1], c[2], c.red());
        runStats.removedLongLits += origSize;
        return true;

    default:
        Lit* at = my_lit_find(c, origLit1);
        if (at != NULL) {
            std::swap(c[0], *at);
        }
        Lit* at2 = my_lit_find(c, origLit2);
        if (at2 != NULL) {
            std::swap(c[1], *at2);
        }
        if (at != NULL && at2 != NULL) {
            delayed_attach_or_free.pop_back();
            if (c.red()) {
                solver->litStats.redLits += c.size();
            } else {
                solver->litStats.irredLits += c.size();
            }
        } else {
            c.setRemoved();
            solver->watches.smudge(origLit1);
            solver->watches.smudge(origLit2);
        }

        runStats.removedLongLits += origSize - c.size();
        return false;
    }

    assert(false);
    return false;
}

void VarReplacer::set_sub_var_during_solution_extension(Var var, const Var sub_var)
{
    const lbool to_set = solver->model[var] ^ table[sub_var].sign();
    const Var sub_var_inter = solver->map_outer_to_inter(sub_var);
    assert(solver->varData[sub_var_inter].removed == Removed::replaced);
    assert(solver->model[sub_var] == l_Undef);

    if (solver->conf.verbosity >= 20) {
        cout << "Varreplace-extend: setting outer " << sub_var+1 << " to " << to_set << " because of " << var+1 << endl;
    }
    solver->model[sub_var] = to_set;
}

void VarReplacer::extend_model(const Var var)
{
    assert(solver->model[var] != l_Undef);
    map<Var, vector<Var> >::const_iterator it
        = reverseTable.find(var);

    if (it == reverseTable.end())
        return;

    assert(it->first == var);
    for(const Var sub_var: it->second)
    {
        set_sub_var_during_solution_extension(var, sub_var);
    }
}

void VarReplacer::extend_model()
{
    if (solver->conf.verbosity >= 20) {
        cout << "c VarReplacer::extend_model() called" << endl;
    }

    assert(solver->model.size() == solver->nVarsOuter());
    for (map<Var, vector<Var> >::const_iterator
        it = reverseTable.begin() , end = reverseTable.end()
        ; it != end
        ; ++it
    ) {
        if (solver->model[it->first] == l_Undef)
            continue;

        for(const Var sub_var: it->second)
        {
            set_sub_var_during_solution_extension(it->first, sub_var);
        }
    }
}

void VarReplacer::replaceChecks(const Var var1, const Var var2) const
{

    assert(solver->ok);
    assert(solver->decisionLevel() == 0);
    assert(solver->value(var1) == l_Undef);
    assert(solver->value(var2) == l_Undef);

    assert(solver->varData[var1].removed == Removed::none);
    assert(solver->varData[var2].removed == Removed::none);
}

bool VarReplacer::handleAlreadyReplaced(const Lit lit1, const Lit lit2)
{
    //OOps, already inside, but with inverse polarity, UNSAT
    if (lit1.sign() != lit2.sign()) {
        (*solver->drup)
        << ~lit1 << lit2 << fin
        << lit1 << ~lit2 << fin
        << lit1 << fin
        << ~lit1 << fin;

        solver->ok = false;
        return false;
    }

    //Already inside in the correct way, return
    return true;
}

bool VarReplacer::replace_vars_already_set(
    const Lit lit1
    , const lbool val1
    , const Lit /*lit2*/
    , const lbool val2
) {
    if (val1 != val2) {
        (*solver->drup)
        << ~lit1 << fin
        << lit1 << fin;

        solver->ok = false;
    }

    //Already set, return with correct code
    return solver->ok;
}

bool VarReplacer::handleOneSet(
    const Lit lit1
    , const lbool val1
    , const Lit lit2
    , const lbool val2
) {
    if (solver->ok) {
        Lit toEnqueue;
        if (val1 != l_Undef) {
            toEnqueue = lit2 ^ (val1 == l_False);
        } else {
            toEnqueue = lit1 ^ (val2 == l_False);
        }
        solver->enqueue(toEnqueue);
        (*solver->drup) << toEnqueue << fin;

        #ifdef STATS_NEEDED
        solver->propStats.propsUnit++;
        #endif

        solver->ok = (solver->propagate<false>().isNULL());
    }
    return solver->ok;
}

/**
@brief Replaces two two lits with one another
*/
bool VarReplacer::replace(
    Var var1
    , Var var2
    , const bool xor_is_true
)
{
    #ifdef VERBOSE_DEBUG
    cout
    << "replace() called with var " <<  Lit(var1, false)
    << " and var " << Lit(var2, false)
    << " with xor_is_true " << xor_is_true << endl;
    #endif

    replaceChecks(var1, var2);

    #ifdef DRUP_DEBUG
    (*solver->drup)
    << Lit(var1, true)  << " " << (Lit(var2, false) ^ xor_is_true) << fin
    << Lit(var1, false) << " " << (Lit(var2, true)  ^ xor_is_true) << fin
    ;
    #endif

    //Move forward
    const Lit lit1 = get_lit_replaced_with(Lit(var1, false));
    const Lit lit2 = get_lit_replaced_with(Lit(var2, false)) ^ xor_is_true;

    //Already inside?
    if (lit1.var() == lit2.var()) {
        return handleAlreadyReplaced(lit1, lit2);
    }
    (*solver->drup)
    << ~lit1 << lit2 << fin
    << lit1 << ~lit2 << fin;

    //None should be removed, only maybe queued for replacement
    assert(solver->varData[lit1.var()].removed == Removed::none);
    assert(solver->varData[lit2.var()].removed == Removed::none);

    const lbool val1 = solver->value(lit1);
    const lbool val2 = solver->value(lit2);

    //Both are set
    if (val1 != l_Undef && val2 != l_Undef) {
        return replace_vars_already_set(lit1, val1, lit2, val2);
    }

    //exactly one set
    if ((val1 != l_Undef && val2 == l_Undef)
        || (val2 != l_Undef && val1 == l_Undef)
    ) {
        return handleOneSet(lit1, val1, lit2, val2);
    }

    assert(val1 == l_Undef && val2 == l_Undef);

    const Lit lit1_outer = solver->map_inter_to_outer(lit1);
    const Lit lit2_outer = solver->map_inter_to_outer(lit2);
    return update_table_and_reversetable(lit1_outer, lit2_outer);
}

bool VarReplacer::update_table_and_reversetable(const Lit lit1, const Lit lit2)
{
    if (reverseTable.find(lit1.var()) == reverseTable.end()) {
        reverseTable[lit2.var()].push_back(lit1.var());
        table[lit1.var()] = lit2 ^ lit1.sign();
        replacedVars++;
        return true;
    }

    if (reverseTable.find(lit2.var()) == reverseTable.end()) {
        reverseTable[lit1.var()].push_back(lit2.var());
        table[lit2.var()] = lit1 ^ lit2.sign();
        replacedVars++;
        return true;
    }

    //both have children
    setAllThatPointsHereTo(lit1.var(), lit2 ^ lit1.sign());
    replacedVars++;
    return true;
}

/**
@brief Changes internal graph to set everything that pointed to var to point to lit
*/
void VarReplacer::setAllThatPointsHereTo(const Var var, const Lit lit)
{
    map<Var, vector<Var> >::iterator it = reverseTable.find(var);
    if (it != reverseTable.end()) {
        for(const Var var2: it->second) {
            assert(table[var2].var() == var);
            if (lit.var() != var2) {
                table[var2] = lit ^ table[var2].sign();
                reverseTable[lit.var()].push_back(var2);
            }
        }
        reverseTable.erase(it);
    }
    table[var] = lit;
    reverseTable[lit.var()].push_back(var);
}

void VarReplacer::checkUnsetSanity()
{
    for(size_t i = 0; i < solver->nVarsOuter(); i++) {
        const Lit repLit = get_lit_replaced_with(Lit(i, false));
        const Var repVar = get_var_replaced_with(i);

        if (solver->varData[i].removed == Removed::none
            && solver->varData[repVar].removed == Removed::none
            && solver->value(i) != solver->value(repLit)
        ) {
            cout
            << "Variable " << (i+1)
            << " has been set to " << solver->value(i)
            << " but it has been replaced with lit "
            << get_lit_replaced_with(Lit(i, false))
            << " and that has been set to "
            << solver->value(get_lit_replaced_with(Lit(i, false)))
            << endl;

            assert(solver->value(i) == solver->value(repLit));
            std::exit(-1);
        }
    }

    #ifdef SLOW_DEBUG
    check_no_replaced_var_set();
    #endif
}

bool VarReplacer::add_xor_as_bins(const BinaryXor& bin_xor)
{
    ps_tmp[0] = Lit(bin_xor.vars[0], false);
    ps_tmp[1] = Lit(bin_xor.vars[1], true ^ bin_xor.rhs);
    solver->add_clause_int(ps_tmp);
    if (!solver->ok) {
        return false;
    }

    ps_tmp[0] = Lit(bin_xor.vars[0], true);
    ps_tmp[1] = Lit(bin_xor.vars[1], false ^ bin_xor.rhs);
    solver->add_clause_int(ps_tmp);
    if (!solver->ok) {
        return false;
    }

    return true;
}

bool VarReplacer::replace_if_enough_is_found(const size_t limit, uint64_t* bogoprops_given)
{
    scc_finder->performSCC(bogoprops_given);
    if (scc_finder->get_num_binxors_found() < limit) {
        scc_finder->clear_binxors();
        return solver->okay();
    }

    const set<BinaryXor>& xors_found = scc_finder->get_binxors();
    for(BinaryXor bin_xor: xors_found) {
        if (!add_xor_as_bins(bin_xor)) {
            return false;
        }

        if (solver->value(bin_xor.vars[0]) == l_Undef
            && solver->value(bin_xor.vars[1]) == l_Undef
        ) {
            replace(bin_xor.vars[0], bin_xor.vars[1], bin_xor.rhs);
            if (!solver->okay()) {
                return false;
            }
        }
    }

    const bool ret = perform_replace();
    if (bogoprops_given) {
        *bogoprops_given += runStats.bogoprops;
    }
    scc_finder->clear_binxors();

    return ret;
}

size_t VarReplacer::mem_used() const
{
    size_t b = 0;
    b += scc_finder->mem_used();
    b += delayedEnqueue.capacity()*sizeof(Lit);
    b += table.capacity()*sizeof(Lit);
    for(map<Var, vector<Var> >::const_iterator
        it = reverseTable.begin(), end = reverseTable.end()
        ; it != end
        ; ++it
    ) {
        b += it->second.capacity()*sizeof(Lit);
    }
    //TODO under-counting
    b += reverseTable.size()*(sizeof(Var) + sizeof(vector<Var>));

    return b;
}

void VarReplacer::print_equivalent_literals(std::ostream *os) const
{
    vector<Lit> tmpCl;
    for (Var var = 0; var < table.size(); var++) {
        const Lit lit = table[var];
        if (lit.var() == var)
            continue;

        tmpCl.clear();
        tmpCl.push_back(~lit);
        tmpCl.push_back(Lit(var, false));
        std::sort(tmpCl.begin(), tmpCl.end());

        *os
        << tmpCl[0] << " "
        << tmpCl[1]
        << " 0\n";

        tmpCl[0] ^= true;
        tmpCl[1] ^= true;

        *os
        << tmpCl[0] << " "
        << tmpCl[1]
        << " 0\n";
    }
}

void VarReplacer::print_some_stats(const double global_cpu_time) const
{
    print_stats_line("c vrep replace time"
        , globalStats.cpu_time
        , stats_line_percent(globalStats.cpu_time, global_cpu_time)
        , "% time"
    );

    print_stats_line("c vrep tree roots"
        , getNumTrees()
    );

    print_stats_line("c vrep trees' crown"
        , get_num_replaced_vars()
        , (double)get_num_replaced_vars()/(double)getNumTrees()
        , "leafs/tree"
    );
}

void VarReplacer::Stats::print(const size_t nVars) const
{
        cout << "c --------- VAR REPLACE STATS ----------" << endl;
        print_stats_line("c time"
            , cpu_time
            , cpu_time/(double)numCalls
            , "per call"
        );

        print_stats_line("c trees' crown"
            , actuallyReplacedVars
            , stats_line_percent(actuallyReplacedVars, nVars)
            , "% of vars"
        );

        print_stats_line("c 0-depth assigns"
            , zeroDepthAssigns
            , stats_line_percent(zeroDepthAssigns, nVars)
            , "% vars"
        );

        print_stats_line("c lits replaced"
            , replacedLits
        );

        print_stats_line("c bin cls removed"
            , removedBinClauses
        );

        print_stats_line("c tri cls removed"
            , removedTriClauses
        );

        print_stats_line("c long cls removed"
            , removedLongClauses
        );

        print_stats_line("c long lits removed"
            , removedLongLits
        );

         print_stats_line("c bogoprops"
            , bogoprops
        );
        cout << "c --------- VAR REPLACE STATS END ----------" << endl;
}

void VarReplacer::Stats::print_short(const Solver* solver) const
{
    cout
    << "c [vrep]"
    << " vars " << actuallyReplacedVars
    << " lits " << replacedLits
    << " rem-bin-cls " << removedBinClauses
    << " rem-tri-cls " << removedTriClauses
    << " rem-long-cls " << removedLongClauses
    << " BP " << bogoprops/(1000*1000) << "M"
    << solver->conf.print_times(cpu_time)
    << endl;
}

VarReplacer::Stats& VarReplacer::Stats::operator+=(const Stats& other)
{
    numCalls += other.numCalls;
    cpu_time += other.cpu_time;
    replacedLits += other.replacedLits;
    zeroDepthAssigns += other.zeroDepthAssigns;
    actuallyReplacedVars += other.actuallyReplacedVars;
    removedBinClauses += other.removedBinClauses;
    removedTriClauses += other.removedTriClauses;
    removedLongClauses += other.removedLongClauses;
    removedLongLits += other.removedLongLits;
    bogoprops += other.bogoprops;

    return *this;
}

void VarReplacer::build_fast_inter_replace_lookup()
{
    fast_inter_replace_lookup.clear();
    fast_inter_replace_lookup.reserve(solver->nVars());
    for(Var var = 0; var < solver->nVars(); var++) {
        fast_inter_replace_lookup.push_back(get_lit_replaced_with(Lit(var, false)));
    }
}

void VarReplacer::destroy_fast_inter_replace_lookup()
{
    vector<Lit> tmp;
    fast_inter_replace_lookup.swap(tmp);
}

Lit VarReplacer::get_lit_replaced_with(Lit lit) const
{
    lit = solver->map_inter_to_outer(lit);
    Lit lit2 = get_lit_replaced_with_outer(lit);
    return solver->map_outer_to_inter(lit2);
}

Lit VarReplacer::get_lit_replaced_with_outer(Lit lit) const
{
    Lit lit2 = table[lit.var()] ^ lit.sign();
    return lit2;
}

Var VarReplacer::get_var_replaced_with(Var var) const
{
    var = solver->map_inter_to_outer(var);
    Var var2 = table[var].var();
    return solver->map_outer_to_inter(var2);
}

vector<Var> VarReplacer::get_vars_replacing(Var var) const
{
    vector<Var> ret;
    var = solver->map_inter_to_outer(var);
    map<Var, vector<Var> >::const_iterator it = reverseTable.find(var);
    if (it != reverseTable.end()) {
        for(Var v: it->second) {
            ret.push_back(solver->map_outer_to_inter(v));
        }
    }

    return ret;
}

vector<pair<Lit, Lit> > VarReplacer::get_all_binary_xors_outer() const
{
    vector<pair<Lit, Lit> > ret;
    for(size_t i = 0; i < table.size(); i++) {
        if (table[i] != Lit(i, false)) {
            ret.push_back(std::make_pair(Lit(i, false), table[i]));
        }
    }

    return ret;
}
