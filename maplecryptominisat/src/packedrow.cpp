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

#include "packedrow.h"

::std::ostream& operator << (std::ostream& os, const CMSat::PackedRow& m)
{
    for(uint32_t i = 0; i < m.getSize()*64; i++) {
        os << m[i];
    }
    os << " -- xor: " << m.is_true();
    return os;
}

using namespace CMSat;

bool PackedRow::operator ==(const PackedRow& b) const
{
    #ifdef DEBUG_ROW
    assert(size > 0);
    assert(b.size > 0);
    assert(size == b.size);
    #endif

    return (std::equal(b.mp-1, b.mp+size, mp-1));
}

bool PackedRow::operator !=(const PackedRow& b) const
{
    #ifdef DEBUG_ROW
    assert(size > 0);
    assert(b.size > 0);
    assert(size == b.size);
    #endif

    return (!std::equal(b.mp-1, b.mp+size, mp-1));
}

uint32_t PackedRow::popcnt() const
{
    uint32_t popcnt = 0;
    for (uint32_t i = 0; i < size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        for (uint32_t i2 = 0; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
    return popcnt;
}

uint32_t PackedRow::popcnt(const uint32_t from) const
{
    uint32_t popcnt = 0;
    for (uint32_t i = from/64; i != size; i++) if (mp[i]) {
        uint64_t tmp = mp[i];
        uint32_t i2;
        if (i == from/64) {
            i2 = from%64;
            tmp >>= i2;
        } else
            i2 = 0;
        for (; i2 < 64; i2++) {
            popcnt += (tmp & 1);
            tmp >>= 1;
        }
    }
    return popcnt;
}

bool PackedRow::fill(vector<Lit>& tmp_clause, const vector<lbool>& assigns, const vector<Var>& col_to_var_original) const
{
    bool final = !is_true_internal;

    tmp_clause.clear();
    uint32_t col = 0;
    bool wasundef = false;
    for (uint32_t i = 0; i < size; i++) for (uint32_t i2 = 0; i2 < 64; i2++) {
        if ((mp[i] >> i2) &1) {
            const Var& var = col_to_var_original[col];
            assert(var != std::numeric_limits<Var>::max());

            const lbool val = assigns[var];
            const bool val_bool = val.getBool();
            tmp_clause.push_back(Lit(var, val_bool));
            final ^= val_bool;
            if (val == l_Undef) {
                assert(!wasundef);
                std::swap(tmp_clause[0], tmp_clause.back());
                wasundef = true;
            }
        }
        col++;
    }
    if (wasundef) {
        tmp_clause[0] ^= final;
        //assert(ps != ps_first+1);
    } else
        assert(!final);

    return wasundef;
}

