/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_integrity_checker.h

Abstract:

    Checker whether the SAT solver internal datastructures 
    are consistent or not.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#pragma once

#include "sat/sat_types.h"
#include "sat/sat_watched.h"

namespace sat {
    class integrity_checker {
        solver const & s;
        bool contains_watched(watch_list const & wlist, clause const & c, clause_offset cls_off) const;
    public:
        integrity_checker(solver const & s);
        
        bool check_clause(clause const & c) const;
        bool check_clauses(clause * const * begin, clause * const * end) const;
        bool check_clauses() const;
        bool check_learned_clauses() const;
        bool check_assignment() const;
        bool check_bool_vars() const;
        bool check_watches() const;
        bool check_watches(literal l, watch_list const& wlist) const;
        bool check_watches(literal l) const;
        bool check_reinit_stack() const;
        bool check_disjoint_clauses() const;
        bool operator()() const;
    };
};
