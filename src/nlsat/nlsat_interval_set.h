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

namespace nlsat {
   // poly bound for local search
   enum poly_bound_state {
      GT, GE, LT, LE, EQ, NEQ
   };
   // poly bound for local search

   struct interval {
        unsigned  m_lower_open:1;
        unsigned  m_upper_open:1;
        unsigned  m_lower_inf:1;
        unsigned  m_upper_inf:1;
        literal   m_justification;
        clause const* m_clause;
        anum      m_lower;
        anum      m_upper;
    };

    class interval_set;

    class interval_set_manager {
        anum m_one, m_zero, m_max, m_min, m_neg_max, m_10k;
        anum_manager &           m_am;
        small_object_allocator & m_allocator;
        svector<char>            m_already_visited;
        random_gen               m_rand;
        void del(interval_set * s);
    public:
        interval_set_manager(anum_manager & m, small_object_allocator & a);
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
                          literal justification, clause const* cls);
        
        /**
           \brief Return the union of two sets.
        */
        interval_set * mk_union(interval_set const * s1, interval_set const * s2);

        interval_set * mk_union(interval_set const * s1, interval_set const * s2, interval_set const * s3);

        // wzh ls
        void set_const_anum();
        interval_set * mk_point_interval(anum const & w);
        interval_set * mk_complement(interval_set const * s);
        interval_set * mk_complement(anum const & w);
        interval_set * mk_intersection(interval_set const * s1, interval_set const * s2);
        interval_set * mk_full();
        bool contains_zero(interval_set const * s) const;
        bool interval_contains_zero(interval inter) const;

        bool peek_in_complement_zero(interval_set const * s, anum & w);
        bool peek_in_complement_lower_int(interval_set const * s, anum & w);
        bool peek_in_complement_lower_far(interval_set const * s, anum & w);
        bool peek_in_complement_upper_int(interval_set const * s, anum & w);
        bool peek_in_complement_upper_far(interval_set const * s, anum & w);
        void peek_in_complement_middle(interval_set const * s, anum_vector & vec);
        void peek_in_complement_threshold(interval_set const * s, anum_vector & vec);
        void peek_in_complement_threshold_integer(interval_set const * s, anum_vector & vec);

        void peek_in_complement_heuristic(interval_set const * s, anum_vector & vec);
        void peek_in_complement_heuristic_level1(interval_set const * s, anum_vector & vec);
        void peek_in_complement_heuristic_level2(interval_set const * s, anum_vector & vec);

        interval_set * mk_bound_interval(anum const & w, poly_bound_state s);
        // hzw ls
        
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

        /**
           \brief Return true if s1 and s2 cover the same subset of R.
           The justifications are ignored
        */
        bool set_eq(interval_set const * s1, interval_set const * s2);
        
        /**
           \brief Return true if s1 and s2 are the same (the justifications are taking into account).
        */
        bool eq(interval_set const * s1, interval_set const * s2);

        /**
           \brief Return a set of literals that justify s.
        */
        void get_justifications(interval_set const * s, literal_vector & js, ptr_vector<clause>& clauses );
        
        std::ostream& display(std::ostream & out, interval_set const * s) const;
        
        unsigned num_intervals(interval_set const * s) const;
        
        /**
           \brief (For debugging purposes) Return one of the intervals in s.
           \pre idx < num_intervals()
        */
        interval_set * get_interval(interval_set const * s, unsigned idx) const;
        
        /**
           \brief Select a witness w in the complement of s.
           
           \pre !is_full(s)
        */
        void peek_in_complement(interval_set const * s, bool is_int, anum & w, bool randomize);
    };

    typedef obj_ref<interval_set, interval_set_manager> interval_set_ref;

    inline std::ostream & operator<<(std::ostream & out, interval_set_ref const & s) {
        s.m().display(out, s);
        return out;
    }

};

