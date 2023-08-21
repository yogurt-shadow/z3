#pragma once

#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_interval_set.h"
#include "util/hashtable.h"
#include "nlsat/nlsat_solver.h"

namespace nlsat {
    using literal_index = var;
    using atom_index    = var;
    using clause_index  = var;
    using interval_set_vector = ptr_vector<interval_set>;
    using lbool_vector        = vector<lbool>;

    using hybrid_var    = var;
    using hybrid_var_vector   = var_vector;

    struct var_hash {
        unsigned operator()(var x) const {
            return x;
        }
    };

    struct var_eq {
        bool operator()(var x, var y) const {
            return x == y;
        }
    };

    using var_table         = hashtable<var, var_hash, var_eq>;
    using bool_var_table    = var_table;
    using hybrid_var_table  = var_table;
    using hybrid_var_pair   = std::pair<var, var>;
    using var_vector_vector = vector<var_vector>;
    using var_table_vector  = vector<var_table>;

    class nlsat_atom {
    private: 
        atom_index           m_index;
        atom *               m_atom;
    public: 
        var_table            m_vars;

        nlsat_atom(atom_index id, atom * at, var_table const & vars): m_index(id), m_atom(at), m_vars(vars)
        {}

        ~nlsat_atom(){}

        unsigned get_index() const {
            return m_index;
        }

        atom * get_atom() const {
            return m_atom;
        }
    };
    

    class nlsat_clause {
    private: 
        clause_index         m_index;
        clause *             m_clause;
    public: 
        var_table            m_vars;
        bool_var_table       m_bool_vars;

        nlsat_clause(clause_index id, clause * cls, var_table const & vars, var_table const & bool_vars): 
            m_index(id), m_clause(cls), m_vars(vars), m_bool_vars(bool_vars) 
        {}

        ~nlsat_clause(){}

        unsigned get_index() const {
            return m_index;
        }

        clause * get_clause() const {
            return m_clause;
        }
    };

    using nlsat_atom_vector   = vector<nlsat_atom *>;
    using nlsat_clause_vector = vector<nlsat_clause *>;
};