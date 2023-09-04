#pragma once

/**
   \brief Implement Watcher for clauses (which may contain both bool and arith variables)

    We use two watching schemes for a clause
   \section  literal watcher (used for BCP)
   \example  a /\ b /\ x + y >= 5
            assigned: {a, b}
            using BCP, we propagate x + y >= 5

   \section variable watcher (used for RCP)
   \example x + y >= 5 /\ yz <= -12
            assigned: {x, z}
            using RCP, we prpagate infeasible set for y

   \ref A Generalized Two-watched-literal Scheme (Tino Teige & Christian Herde, EPIA'2007)
*/

#include "nlsat/nlsat_advanced_types.h"

namespace nlsat {
    /**
      \brief Implement arith var watcher for arith literals
    */
    class atom_var_watcher {
    public:
        unsigned              m_atom_index;
        var                   v1, v2;

        atom_var_watcher(unsigned idx, var _v1, var _v2): m_atom_index(idx), v1(_v1), v2(_v2) {}
        ~atom_var_watcher() {}

        var get_another_var(var v) const {
          SASSERT(v == v1 || v ==  v2);
          return v == v1 ? v2 : v1;
        }

        void replace_var(var old_var, var new_var) {
          SASSERT(old_var == v1 || old_var == v2);
          if(old_var == v1) {
            v1 = new_var;
          } else {
            v2 = new_var;
          }
        }
    };


    /**
      \brief Implement hybrid var watcher for whole clause
    */
    class clause_var_watcher {
    public:
        unsigned              m_clause_index;
        hybrid_var            v1, v2;
        bool                  updated, deleted; // used when deleting learned clauses

        clause_var_watcher(unsigned idx, hybrid_var _v1, hybrid_var _v2): m_clause_index(idx), v1(_v1), v2(_v2), updated(true), deleted(false) {}
        ~clause_var_watcher() {}

        hybrid_var get_another_var(hybrid_var v) const {
          SASSERT(v == v1 || v == v2);
          return v == v1 ? v2 : v1;
        }

        void replace_var(hybrid_var old_var, hybrid_var new_var){
          SASSERT(old_var == v1 || old_var == v2);
          if (old_var == v1) {
            v1 = new_var;
          }
          else {
            v2 = new_var;
          }
        }

        unsigned size() const {
          return (v1 != null_var) + (v2 != null_var);
        }
    };

    /**
      \brief Implement literal watcher for whole clause
      \note using int to declare positive or negative literal
    */
    class clause_literal_watcher {
    public:
        unsigned             m_clause_index;
        int                  l1, l2;

        clause_literal_watcher(unsigned idx, int _l1, int _l2): m_clause_index(idx), l1(_l1), l2(_l2) {}
        ~clause_literal_watcher() {}

        int get_another_literal_index_using_abs(unsigned l) const {
          SASSERT(l == std::abs(l1) || l == std::abs(l2));
          return l == std::abs(l1) ? l2 : l1;
        }

        void replace_literal(int old_id, int new_id) {
          SASSERT(old_id == l1 || old_id == i2);
          if (old_id == l1) {
            l1 = new_id;
          } else {
            l2 = new_id;
          }
        }

        void replace_literal_using_abs(unsigned old_id, int new_id) {
          if(std::abs(l1) == old_id) {
            l1 = new_id;
          } else if(std::abs(l2) == old_id) {
            l2 = new_id;
          } else {
            UNREACHABLE();
          }
        }
    };

    /**
      \brief When does a learnt clause is unit to a var
      case 1: all poly vars are assigned, only left one root var (which do not occur in other root atom's poly var) unassigned
      \example x > atom(x^3 * y^2 + 5 x^2 -8 >= 0, 2) \/ x y z <= -1    [y assigned], unit to x
      case 2: all root vars are assigned, left one hybrid var unassigned which is not in any root_atom's poly
      \example x > atom(x^3 * y^2 + 5 x^2 -8 >= 0, 2) \/ x z <= -1    [x, y assigned], unit to z

      \note Algorithm: Still use two hybrid watcher for learned clause
      when a var is assigned, find another unassigned var
      \if not find, determine whether another watched var is qualified, if yes, set unit
      \else find, change watch
    */
};