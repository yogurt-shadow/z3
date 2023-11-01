/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_interval_set.h

Abstract:

    Sets of disjoint infeasible intervals.

Author:

    Leonardo de Moura (leonardo) 2012-01-11.

Revision History:

--*/
#pragma once

#include "nlsat/nlsat_types.h"
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_solver.h"

namespace nlsat {
   struct interval {
        unsigned  m_lower_open:1;
        unsigned  m_upper_open:1;
        unsigned  m_lower_inf:1;
        unsigned  m_upper_inf:1;
        anum      m_lower;
        anum      m_upper;
        literal   m_justification; // unsat literal
        clause *  m_clause; // where the literal came from
    };

    class interval_set;
    using interval_set_vector = ptr_vector<interval_set>;

    class interval_set_manager {
        clause_table  curr_clauses;
        anum m_one, m_zero, m_max, m_min, m_neg_max, m_10k;
        anum_manager &           m_am;
        small_object_allocator & m_allocator;
        svector<char>            m_already_visited;
        random_gen               m_rand;
        solver                 & m_solver;
        void del(interval_set * s);
    public:
        interval_set_manager(anum_manager & m, small_object_allocator & a, solver &sol);
        ~interval_set_manager();
        
        void set_seed(unsigned s) { m_rand.set_seed(s); }

        /**
           \brief Return the empty set.
        */
        interval_set * mk_empty() { return nullptr; }
        
        /**
           \brief Return a set of composed of a single interval.
        */
        interval_set * mk(bool lower_open, bool lower_inf, anum const & lower, 
                          bool upper_open, bool upper_inf, anum const & upper,
                          literal justification, clause * cls);
        
        /**
           \brief Return the union of two sets.
        */
        interval_set * mk_union(interval_set const * s1, interval_set const * s2);

        interval_set * mk_union(interval_set const * s1, interval_set const * s2, interval_set const * s3);

        void set_const_anum();
        interval_set * mk_point_interval(anum const & w);
        interval_set * mk_complement(interval_set const * s);
        interval_set * mk_complement(anum const & w, literal jst, clause *cls);
        interval_set * mk_intersection(interval_set const * s1, interval_set const * s2);
        interval_set * mk_full();
        bool contains_zero(interval_set const * s) const;
        bool interval_contains_zero(interval inter) const;
        bool contains(interval_set const* s, anum const& w) const;
        bool interval_contains(interval inter, anum const &w) const;
        
        /**
           \brief Reference counting
        */
        void dec_ref(interval_set * s);
        void inc_ref(interval_set * s);
        
        /**
           \brief Return true if s is the empty set.
        */
        bool is_empty(interval_set const * s) {
            return s == nullptr;
        }
        
        /**
           \brief Return true if the set contains all real numbers.
        */
        bool is_full(interval_set const * s);

        /**
           `\brief Return true if s1 is a subset of s2.
        */
        bool subset(interval_set const * s1, interval_set const * s2);

        bool is_union_full(interval_set const *s1, interval_set const *s2);

        /**
           \brief Return true if s1 and s2 cover the same subset of R.
           The justifications are ignored
        */
        bool set_eq(interval_set const * s1, interval_set const * s2);
        
        /**
           \brief Return true if s1 and s2 are the same (the justifications and clauses are taking into account).
        */
        bool eq(interval_set const * s1, interval_set const * s2);
        
        std::ostream& display(std::ostream & out, interval_set const * s) const;
        
        unsigned num_intervals(interval_set const * s) const;
        
        /**
           \brief (For debugging purposes) Return one of the intervals in s.
           \pre idx < num_intervals()
        */
        interval_set * get_interval(interval_set const * s, unsigned idx) const;
        bool atom_contributed(interval_set const *s, bool_var bvar) const;
        void set_clauses(interval_set *s, clause *cls);
        void get_clauses(interval_set const *s, clause_vector &clauses);

        /**
           \brief Select a witness w in the complement of s.
           
           \pre !is_full(s)
        */
        void peek_in_complement(interval_set const * s, bool is_int, anum & w, bool randomize);
        std::ostream & display_interval(std::ostream & out, interval const & curr) const;
    };

    typedef obj_ref<interval_set, interval_set_manager> interval_set_ref;

    inline std::ostream & operator<<(std::ostream & out, interval_set_ref const & s) {
        s.m().display(out, s);
        return out;
    }

};

