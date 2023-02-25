/**
 * @brief advanced data structures for nlsat
 * * 1. nlsat bool var: 
 * * 2. nlsat arith var: 
 * * 2. nlsat literal: 
 * * . nlsat atom: index, atom, arith vars
 * * . nlsat clause: index, clause, bool vars, arith vars, watched var
*/

#pragma once

#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_interval_set.h"
#include "util/hashtable.h"

namespace nlsat {
    using stage_var                    =                    var;
    using literal_index                =                    var;
    using atom_index                   =                    var;
    using clause_index                 =                    var;
    using hybrid_var                   =                    var;
    using hybrid_var_vector            =                    var_vector;
    using interval_set_vector          =                    ptr_vector<interval_set>;
    using lbool_vector                 =                    vector<lbool>;

    // hastable for var
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

    using var_table                    =                    hashtable<var, var_hash, var_eq>;
    using bool_var_table               =                    var_table;
    using hybrid_var_table             =                    var_table;
    using hybrid_var_pair              =                    std::pair<var, var>;
    using var_vector_vector            =                    vector<var_vector>;
    using var_table_vector             =                    vector<var_table>;

    /**
     * @brief atom class
     * ^ m_index: index of atom
     * ^ m_atom: atom pointer
     * ^ m_vars: arith vars of this atom
    */
    class nlsat_atom {
    private:
        atom_index m_index;
        atom * m_atom;
    public:
        var_table m_vars;

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
    
    /**
     * @brief clause class
     * ^ m_index: index of clause
     * ^ m_clause: clause pointer
     * ^ m_vars: arith vars
     * ^ m_bool_vars: bool vars
     * ^ m_watched_var: watched vars (bool or theory)
     * 
    */
    class nlsat_clause {
    private:
        clause_index m_index;
        clause * m_clause;
    public:
        var_table m_vars;
        bool_var_table m_bool_vars;
        hybrid_var_pair m_watched_var;

        nlsat_clause(clause_index id, clause * cls, var_table const & vars, var_table const & bool_vars): 
            m_index(id), m_clause(cls), m_vars(vars), m_bool_vars(bool_vars) 
        {
            m_watched_var = hybrid_var_pair(null_var, null_var);
        }

        ~nlsat_clause(){}

        unsigned get_index() const {
            return m_index;
        }

        clause * get_clause() const {
            return m_clause;
        }

        void set_watched_var(hybrid_var x, hybrid_var y) {
            m_watched_var.first = x;
            m_watched_var.second = y;
        }

        var get_another_watched_var(hybrid_var x) const {
            SASSERT(m_watched_var.first == x || m_watched_var.second == x);
            return m_watched_var.first - x + m_watched_var.second;
        }
    };

    using nlsat_atom_vector             =                vector<nlsat_atom *>;
    using nlsat_clause_vector           =                vector<nlsat_clause *>;
};