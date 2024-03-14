#pragma once

#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_interval_set.h"

namespace nlsat {
    class caching_system {
    private:
        atom_vector            const &m_atoms;
        clause_vector          const &m_clauses;
        vector<var_vector>     const &m_var_literals;
        vector<var_vector>     const &m_literal_clauses;

    public:
        caching_system(atom_vector const &_atoms, clause_vector const &_clauses, vector<var_vector> const &var_literals, vector<var_vector> const &literal_clauses):
            m_atoms(_atoms), m_clauses(_clauses), m_var_literals(var_literals), m_literal_clauses(literal_clauses) {}

        ~caching_system() {}

        
    };
};