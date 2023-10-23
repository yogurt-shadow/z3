/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_clause.h

Abstract:

    Clauses used in the Nonlinear arithmetic satisfiability procedure. 

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#pragma once

#include "nlsat/nlsat_types.h"
#include "util/vector.h"
#include "util/chashtable.h"

namespace nlsat {
    class clause {
        friend class solver;
        unsigned         m_id;
        unsigned         m_nlsat_id;
        unsigned         m_size;
        unsigned         m_capacity:31;
        unsigned         m_learned:1;
        double           m_activity;
        assumption_set   m_assumptions;
        literal          m_lits[0];
        static size_t get_obj_size(unsigned num_lits) { return sizeof(clause) + num_lits * sizeof(literal); }
        size_t get_size() const { return get_obj_size(m_capacity); }
        clause(unsigned id, unsigned id2, unsigned sz, literal const * lits, bool learned, assumption_set as);
    public:
        unsigned size() const { return m_size; }
        bool is_unit() const { return size() == 1; }
        unsigned id() const { return m_id; }
        unsigned nlsat_id() const { return m_nlsat_id; }
        literal & operator[](unsigned idx) { SASSERT(idx < m_size); return m_lits[idx]; }
        literal const & operator[](unsigned idx) const { SASSERT(idx < m_size); return m_lits[idx]; }
        bool is_learned() const { return m_learned; }
        literal * begin() { return m_lits; }
        literal * end() { return m_lits + m_size; }
        literal const * begin() const { return m_lits; }
        literal const * end() const { return m_lits + m_size; }
        literal const * data() const { return m_lits; }
        void inc_activity() { m_activity++; }
        void set_activity(double v) {m_activity = v; }
        double get_activity() const { return m_activity; }
        bool contains(literal l) const;
        bool contains(bool_var v) const;
        void shrink(unsigned num_lits) { SASSERT(num_lits <= m_size); if (num_lits < m_size) { m_size = num_lits; } }
        assumption_set assumptions() const { return m_assumptions; }
        struct hash_proc {
            unsigned operator()(clause const *cls) const {
                return cls->is_learned() ? 2 * cls->id() + 1 : 2 * cls->id();
            }
        };

        struct eq_proc {
            bool operator()(clause const *c1, clause const *c2) const {
                return c1->id() == c2->id() && c1->is_learned() == c2->is_learned();
            }
        };
    };

    typedef ptr_vector<clause> clause_vector;
    typedef chashtable<clause*, clause::hash_proc, clause::eq_proc> clause_table;
};

