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

#ifndef VARREPLACER_H
#define VARREPLACER_H

#include <map>
#include <vector>
#include <utility>

#include "constants.h"
#include "solvertypes.h"
#include "clause.h"
#include "watcharray.h"

namespace CMSat {

//#define VERBOSE_DEBUG

using std::map;
using std::vector;
class Solver;
class SCCFinder;

/**
@brief Replaces variables with their anti/equivalents
*/
class VarReplacer
{
    public:
        VarReplacer(Solver* solver);
        ~VarReplacer();
        void new_var(const Var orig_outer);
        void new_vars(const size_t n);
        void save_on_var_memory();
        bool replace_if_enough_is_found(const size_t limit = 0, uint64_t* bogoprops = NULL);
        void print_equivalent_literals(std::ostream *os) const;
        void print_some_stats(const double global_cpu_time) const;
        const SCCFinder* get_scc_finder() const;

        void extend_model();
        void extend_model(const Var var);

        Var get_var_replaced_with(const Var var) const;
        Var get_var_replaced_with(const Lit lit) const;
        Lit get_lit_replaced_with(Lit lit) const;
        Lit get_lit_replaced_with_outer(Lit lit) const;

        vector<Var> get_vars_replacing(Var var) const;
        void updateVars(
            const vector<uint32_t>& outerToInter
            , const vector<uint32_t>& interToOuter
        );

        //Stats
        size_t get_num_replaced_vars() const;
        struct Stats
        {
            void clear()
            {
                Stats tmp;
                *this = tmp;
            }

            Stats& operator+=(const Stats& other);
            void print(const size_t nVars) const;
            void print_short(const Solver* solver) const;

            uint64_t numCalls = 0;
            double cpu_time = 0;
            uint64_t replacedLits = 0;
            uint64_t zeroDepthAssigns = 0;
            uint64_t actuallyReplacedVars = 0;
            uint64_t removedBinClauses = 0;
            uint64_t removedTriClauses = 0;
            uint64_t removedLongClauses = 0;
            uint64_t removedLongLits = 0;
            uint64_t bogoprops = 0;
        };
        const Stats& get_stats() const;
        size_t mem_used() const;
        vector<std::pair<Lit, Lit> > get_all_binary_xors_outer() const;

    private:
        Solver* solver;
        SCCFinder* scc_finder;
        vector<Clause*> delayed_attach_or_free;

        void check_no_replaced_var_set() const;
        vector<Lit> fast_inter_replace_lookup;
        void build_fast_inter_replace_lookup();
        void destroy_fast_inter_replace_lookup();
        Lit get_lit_replaced_with_fast(const Lit lit) const {
            return fast_inter_replace_lookup[lit.var()] ^ lit.sign();
        }
        Var get_var_replaced_with_fast(const Var var) const {
            return fast_inter_replace_lookup[var].var();
        }

        vector<Lit> ps_tmp;
        bool perform_replace();
        bool add_xor_as_bins(const BinaryXor& bin_xor);
        bool replace(
            Var lit1
            , Var lit2
            , bool xor_is_true
        );

        bool isReplaced(const Var var) const;
        bool isReplaced(const Lit lit) const;
        bool isReplaced_fast(const Var var) const;
        bool isReplaced_fast(const Lit lit) const;

        size_t getNumTrees() const;
        void set_sub_var_during_solution_extension(Var var, Var sub_var);
        void checkUnsetSanity();

        bool replace_set(vector<ClOffset>& cs);
        void attach_delayed_attach();
        void update_all_vardata_activities();
        void update_vardata_and_activities(
            const Var orig
            , const Var replaced
        );
        bool enqueueDelayedEnqueue();

        //Helpers for replace()
        void replaceChecks(const Var var1, const Var var2) const;
        bool handleAlreadyReplaced(const Lit lit1, const Lit lit2);
        bool replace_vars_already_set(
            const Lit lit1
            , const lbool val1
            , const Lit lit2
            , const lbool val2
        );
        bool handleOneSet(
            const Lit lit1
            , const lbool val1
            , const Lit lit2
            , const lbool val2
        );

        //Temporary used in replaceImplicit
        vector<BinaryClause> delayed_attach_bin;
        bool replaceImplicit();
        struct ImplicitTmpStats
        {
            ImplicitTmpStats() :
                removedRedBin(0)
                , removedIrredBin(0)
                , removedRedTri(0)
                , removedIrredTri(0)
            {
            }

            void remove(const Watched& ws)
            {
                if (ws.isTri()) {
                    if (ws.red()) {
                        removedRedTri++;
                    } else {
                        removedIrredTri++;
                    }
                } else if (ws.isBinary()) {
                    if (ws.red()) {
                        removedRedBin++;
                    } else {
                        removedIrredBin++;
                    }
                } else {
                    assert(false);
                }
            }

            void clear()
            {
                *this = ImplicitTmpStats();
            }

            size_t removedRedBin;
            size_t removedIrredBin;
            size_t removedRedTri;
            size_t removedIrredTri;
        };
        ImplicitTmpStats impl_tmp_stats;
        void updateTri(
            watch_subarray::iterator& i
            , watch_subarray::iterator& j
            , const Lit origLit1
            , const Lit origLit2
            , Lit lit1
            , Lit lit2
        );
        void updateBin(
            watch_subarray::iterator& i
            , watch_subarray::iterator& j
            , const Lit origLit1
            , const Lit origLit2
            , Lit lit1
            , Lit lit2
        );
        void newBinClause(
            Lit origLit1
            , Lit origLit2
            , Lit origLit3
            , Lit lit1
            , Lit lit2
            , bool red
        );
        void updateStatsFromImplStats();

        bool handleUpdatedClause(Clause& c, const Lit origLit1, const Lit origLit2);

         //While replacing the implicit clauses we cannot enqeue
        vector<Lit> delayedEnqueue;
        bool update_table_and_reversetable(const Lit lit1, const Lit lit2);
        void setAllThatPointsHereTo(const Var var, const Lit lit);

        //Mapping tables
        vector<Lit> table; ///<Stores which variables have been replaced by which literals. Index by: table[VAR]
        map<Var, vector<Var> > reverseTable; ///<mapping of variable to set of variables it replaces

        //Stats
        void printReplaceStats() const;
        uint64_t replacedVars = 0; ///<Num vars replaced during var-replacement
        uint64_t lastReplacedVars = 0;
        Stats runStats;
        Stats globalStats;
};

inline size_t VarReplacer::get_num_replaced_vars() const
{
    return replacedVars;
}

inline bool VarReplacer::isReplaced(const Var var) const
{
    return get_var_replaced_with(var) != var;
}

inline bool VarReplacer::isReplaced_fast(const Var var) const
{
    return get_var_replaced_with_fast(var) != var;
}

inline Var VarReplacer::get_var_replaced_with(const Lit lit) const
{
    return get_var_replaced_with(lit.var());
}

inline bool VarReplacer::isReplaced(const Lit lit) const
{
    return isReplaced(lit.var());
}

inline bool VarReplacer::isReplaced_fast(const Lit lit) const
{
    return isReplaced_fast(lit.var());
}

inline size_t VarReplacer::getNumTrees() const
{
    return reverseTable.size();
}

inline const VarReplacer::Stats& VarReplacer::get_stats() const
{
    return globalStats;
}

inline const SCCFinder* VarReplacer::get_scc_finder() const
{
    return scc_finder;
}

} //end namespace

#endif //VARREPLACER_H
