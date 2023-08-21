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
*/

#include "nlsat/nlsat_advanced_types.h"

namespace nlsat {
    /**
      \brief Implement arith var watcher for arith atom
    */
    class atom_watcher {
    public:
        atom_index            m_atom_index;
        var                   another_arith_var;

        atom_watcher(atom_index idx, var another): m_atom_index(idx), another_arith_var(another) {}
        ~atom_watcher() {}
    };


    /**
      \brief Implement hybrid var watcher for whole clause
    */
    class clause_var_watcher {
    public:
        clause_index          m_clause_index;
        hybrid_var            another_hybrid_var;

        clause_var_watcher(clause_index idx, hybrid_var another): m_clause_index(idx), another_hybrid_var(another) {}
        ~clause_var_watcher() {}
    };

    /**
      \brief Implement literal watcher for whole clause
      \note using int to declare positive or negative literal
    */
    class clause_literal_watcher {
    public:
        clause_index         m_clause_index;
        int                  another_literal_index;

        clause_literal_watcher(clause_index idx, int another): m_clause_index(idx), another_literal_index(another) {}
        ~clause_literal_watcher() {}
    };
};