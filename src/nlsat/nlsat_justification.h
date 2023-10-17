/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_justification.h

Abstract:

    An explanation for a (Boolean) assignment in the 
    nlsat procedure

Author:

    Leonardo de Moura (leonardo) 2012-01-10.

Revision History:

--*/
#pragma once

#include "nlsat/nlsat_types.h"
#include "util/tptr.h"

namespace nlsat {
    class clause_lazy_justification {
        literal l;
        clause_vector m_clauses;
    public:
        clause_lazy_justification(literal const &_l, clause_vector const& vec): l(_l), m_clauses(vec) {}
        literal get_literal() const {
            return l;
        }
        unsigned num_clauses() const { return m_clauses.size(); }
        nlsat::clause const &clause(unsigned i) const
        {
            return *(m_clauses[i]);
        }
    };

    class justification {
        void * m_data;
    public:
        enum kind { NULL_JST = 0, DECISION, CLAUSE, CLAUSE_LAZY };
        justification():m_data(TAG(void *, nullptr, NULL_JST)) { SASSERT(is_null()); }
        justification(bool):m_data(TAG(void *, nullptr, DECISION)) { SASSERT(is_decision()); }
        justification(clause * c):m_data(TAG(void *, c, CLAUSE)) { SASSERT(is_clause()); }
        justification(clause_lazy_justification * j):m_data(TAG(void *, j, CLAUSE_LAZY)) { SASSERT(is_lazy()); }
        kind get_kind() const { return static_cast<kind>(GET_TAG(m_data)); }
        bool is_null() const { return get_kind() == NULL_JST; }
        bool is_decision() const { return get_kind() == DECISION; }
        bool is_clause() const { return get_kind() == CLAUSE; }
        bool is_clause_lazy() const { return get_kind() == CLAUSE_LAZY; }
        clause * get_clause() const { return UNTAG(clause*, m_data); }
        clause_lazy_justification * get_lazy() const { return UNTAG(clause_lazy_justification*, m_data); }
        bool operator==(justification other) const { return m_data == other.m_data; }
        bool operator!=(justification other) const { return m_data != other.m_data; }
    };

    inline std::ostream& operator<<(std::ostream& out, justification::kind k) {
        switch (k) {
        case justification::NULL_JST: return out << "null";
        case justification::DECISION: return out << "decision";
        case justification::CLAUSE: return out << "clause";
        case justification::CLAUSE_LAZY: return out << "lazy";
        default: return out << "??";
        }
    }
    
    const justification null_justification;
    const justification decided_justification(true);

    inline justification mk_clause_jst(clause const * c) { return justification(const_cast<clause*>(c)); }
    inline justification mk_clause_lazy_jst(literal const &l, clause_vector const& vec) {
        return justification(new clause_lazy_justification(l, vec));
    }
};

