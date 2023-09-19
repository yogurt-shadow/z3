#pragma once

#include "nlsat/nlsat_watcher.h"
#include "util/hashtable.h"
#include "nlsat/nlsat_solver.h"

namespace nlsat {
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

    struct type_var {
        var  v;
        bool is_bool;

        type_var() {}
        type_var(var _v, bool _b): v(_v), is_bool(_b) {}
        
        type_var& operator=(type_var const& other) {
            v = other.v;
            is_bool = other.is_bool;
            return *this;
        }
    };

    struct type_var_hash {
        unsigned operator()(type_var const& tv) const {
            return tv.is_bool ? 2 * tv.v : 2 * tv.v + 1;
        }
    };

    struct type_var_eq {
        bool operator()(type_var const &tv1, type_var const &tv2) const {
            return tv1.is_bool == tv2.is_bool && tv1.v == tv2.v;
        }
    };

    using type_var_table    = hashtable<type_var, type_var_hash, type_var_eq>;

    class nlsat_atom {
    private: 
        unsigned             m_index;
        atom *               m_atom;
    public: 
        var_table            m_vars;
        atom_var_watcher    *m_var_watcher;
        
        nlsat_atom(unsigned id, atom * at, var_table const & vars): m_index(id), m_atom(at), m_vars(vars), m_var_watcher(nullptr)
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
        unsigned             m_index;
        clause *             m_clause;
    public: 
        var_table            m_vars;
        bool_var_table       m_bool_vars;
        clause_var_watcher  *m_var_watcher;
        clause_literal_watcher *m_atom_watcher;

        nlsat_clause(unsigned id, clause * cls, var_table const & vars, var_table const & bool_vars): 
            m_index(id), m_clause(cls), m_vars(vars), m_bool_vars(bool_vars), m_var_watcher(nullptr), m_atom_watcher(nullptr)
        {}
        ~nlsat_clause(){}

        unsigned get_index() const {
            return m_index;
        }

        clause * get_clause() const {
            return m_clause;
        }
    };

    /**
      \brief When does a learnt clause is unit to a var
      case 1: all poly vars are assigned, only left one root var (which do not occur in other root atom's poly var) unassigned
      \example x > atom(x^3 * y^2 + 5 x^2 -8 >= 0, 2) \/ x y <= -1    [y assigned], unit to x
      case 2: all root vars are assigned, left one hybrid var unassigned which is not in any root_atom's poly
      \example x > atom(x^3 * y^2 + 5 x^2 -8 >= 0, 2) \/ x z <= -1    [x, y assigned], unit to z

      \note Algorithm: Still use two hybrid watcher for learned clause
      when a var is assigned, find another unassigned var
      \if not find, determine whether another watched var is qualified, if yes, set unit
      \else find, change watch

      \param bool_vars: overall bool var
             arith_vars: overall arith vars
             root_except_rp_vars: root_var (which do not occur in other root atom's poly var)
             poly_except_rp_vars: poly_var of ineq (which do not occur in other root atom's poly var)
    */
    class nlsat_learned {
    public:
        unsigned            m_index;
        clause *            m_clause;
        bool_var_table      m_bool_vars;
        var_table           m_arith_vars;
        var_table           m_rp_vars;
        clause_var_watcher  *m_var_watcher;
        clause_literal_watcher *m_atom_watcher;

        nlsat_learned(unsigned id, clause * cls, bool_var_table const &bvars, var_table const &avars, var_table const& rp_vars):
            m_index(id), m_clause(cls), m_bool_vars(bvars), m_arith_vars(avars), m_rp_vars(rp_vars), m_var_watcher(nullptr), m_atom_watcher(nullptr)
        {

        }
    };

    using nlsat_atom_vector    = vector<nlsat_atom *>;
    using nlsat_clause_vector  = vector<nlsat_clause *>;
    using nlsat_learned_vector = vector<nlsat_learned *>;
};