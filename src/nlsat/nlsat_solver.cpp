/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_solver.cpp

Abstract:

    Nonlinear arithmetic satisfiability procedure.  The procedure is
    complete for nonlinear real arithmetic, but it also has limited
    support for integers.

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/

/**
 * ---------------------------------------------------------------------------------------------------------------
 * @name HDnlsat: Hybrid Dynamic Nonlinear Arithmetic Satisfiability Procedure
 * @date start time: 2022/09/23
 * @author Zhonghan Wang (wzh)
 * @brief This version supports arbitrary order of hybrid boolean var and arith var
 *
 * @note Implementation Note
 * ------------------- version 1 -------------------
 * 1. Do not distinguish hybrid vars (bool var and arith var) when watching, doing or undoing clauses
 * 2. Add new trail kind
 *    2.1 Pick Bool Var: select a new bool var to process
 *    2.2 Arith Assignment: select witness for arith var at the end of process clauses
 * 3. Adjust search mode in resolve:
 *    3.1 All assigned, search mode aribitrary, new clause triggered new conflict, continue resolution
 *    3.2 Only left bool var, search mode bool
 *    3.3 Only left arith var, search mode arith
 *    3.4 left two unassigned vars, unreachable
 * 4. New Stage at the end of arith assignment (m_xk = num_arith_vars())
 * 5. Register new stage when switching mode
 * 6. unit propagate after assignment
 *
 * @version
 * version1 (2022/10/02)
 * version2 (2022/10/05)
 * 
 * ------------------- version 2 -------------------
 * @date 2023/08/24
 * @todo 1. new watcher implement
 *       2. clause infeasible
 *       3. phase saving for inconnectivity variables
 *       4. lbd delete strategy
 *
 * @note Question about justification of clause infeasible
 *
 * @date 2023/08/26
 * @note 1. should we decide literals after considering clause infeasible ?
 *       2. should we assign arith literal when unit propagation (is it useful ?)
 *      \example x + y + z >= 12 \/ b \/ c
 *      [b, c] we can propagate x + y + z >= 12, while this literal is useless until it is arith-unit
 *      [x, y, z, b] we can unit propagate c
 * 
 * @date 2023/09/05
 * @note When we update clause infeasible set for an arith var, if we encounter a conflict, what should we do ?
 *       Some basic idea:
 *       I. Assume first k clauses didn't overlap R, then if we reprocess them, there won't be any conflict
 *          Moreover, the infeasible set won't change larger when we reprocess them (maybe smaller due to semantics decision)
 *       II. The kth clause is the conflict clause, num_undef will be zero
 *       III. Implementation: do not convert infeasible set to nullptr, just process and do semantics decision, save update infeasible trail,
 *            and use that infeasible trail to detect atom status as usual, the conflict clause should be propagated false.
 * 
 * @date 2023/09/11
 * @brief Question about unit propagate and R_propagate when resolving
 * @example y^2 - x^2 + 4 < 0          [x -> 0]
 *          We first propagate the literal using unit propagate. Then, we assign x -> 0, which R propagates literal to be false.
 *          When resolving conflict, we found that the literal is assigned by UP and thus learn an empty clause.
 *          In this case, we prove unsat and this is totally wrong.
 * @note    Current version does not support assignment by unit propagate, 
 * 
 * @date 2023/09/11
 * @brief Add watcher for vars, atoms and clauses (lemmas) incrementally
 * 
 * @date 2023/09/13
 * @brief Add frontend processing and information caching when reseting
 * @brief Change infeasible cache dynamicly
 * 
 * @date 2023/09/14
 * @brief set watcher pointer in watched structures, useful when deleting
 * @brief literal negation when making complement for interval sets
 * @brief unit checker for root atom, propagate newly added atoms when registering new lemma
 * 
 * @date 2023/09/20
 * @brief Unit Propagate rather than using lazy propagate
 * @example x >= 3
 *          previous: update x: [3, +oo], then we propagate the literal
 *          current: if the atom's updated infeasible set does not trigger conflict, assign it with unit propagate
 *          Remember when we update infeasible set each time, propagate unit arith atom as soon as possible
 * 
 * @brief Special case when we face a conflict
 * @example x >= 3, y <= 4, x = -12 \/ y = 8
 *          When we update infeasible set in first two clauses, infeasible set propagates
 *          atoms in clause 3 to be false, and this is a conflict clause detected by unit propagate part.
 *          However, we found no decision and all vars are unassigned, in this case we just return unsat.
 * 
 * @date 2023/09/21
 * @brief Tackling with special case
 * @example y >= 23, z <= 18, y < x + 10 \/ z > x + 30
 *          we propagate infeasible y -> (-oo, 23) z -> (18, +oo)
 *          assume we branch x and assign it to x -> 0
 *          then we propagate atom as soon as possible and get clause 3 a conflict
 *          In this case, we should update stage and choose values for unassigned var 
 *          until the clause has only one unassigned var
 * 
 * @date 2023/09/22
 * @brief Decision level for arith literals
 * @example y > 24, a \/ x^2 + y < 12 with [a -> false, x -> 0]
 * @note    we face a conflict when we are processing arith var y,
 *          but the assigned literal y > 24 is assigned at the start of search,
 *          after that we decide a bool var, which increases the overall level
 *          in this case, the literal y > 24 is the same stage, but not the same level of current status,
 *          then process antecedent won't increase mark and cause bugs
 * @note We use arith level to record semantics level for an arith var
 * ---------------------------------------------------------------------------------------------------------------
 **/

#include "util/z3_exception.h"
#include "util/chashtable.h"
#include "util/id_gen.h"
#include "util/map.h"
#include "util/dependency.h"
#include "util/permutation.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial_cache.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_justification.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_explain.h"
#include "nlsat/nlsat_params.hpp"

#include "nlsat_watcher.h"
#include "nlsat_branching.h"
#include "nlsat_options.h"
#include "util/heap.h"
#include <cmath>
#include <stdlib.h>

#include <iostream>

#define NLSAT_EXTRA_VERBOSE

#ifdef NLSAT_EXTRA_VERBOSE
#define NLSAT_VERBOSE(CODE) IF_VERBOSE(10, CODE)
#else
#define NLSAT_VERBOSE(CODE) ((void)0)
#endif

namespace nlsat {
    typedef chashtable<ineq_atom*, ineq_atom::hash_proc, ineq_atom::eq_proc> ineq_atom_table;
    typedef chashtable<root_atom*, root_atom::hash_proc, root_atom::eq_proc> root_atom_table;

    // for apply_permutation procedure
    void swap(clause * & c1, clause * & c2) {
        std::swap(c1, c2);
    }

    struct solver::ctx {
        params_ref             m_params;
        reslimit&              m_rlimit;
        small_object_allocator m_allocator;
        unsynch_mpq_manager    m_qm;
        pmanager               m_pm;
        anum_manager           m_am;
        bool                   m_incremental;
        ctx(reslimit& rlim, params_ref const & p, bool incremental):
            m_params(p),
            m_rlimit(rlim),
            m_allocator("nlsat"),
            m_pm(rlim, m_qm, &m_allocator),
            m_am(rlim, m_qm, p, &m_allocator),
            m_incremental(incremental)
        {}
    };

    struct solver::imp {
        struct dconfig {
            typedef imp                      value_manager;
            typedef small_object_allocator   allocator;
            typedef void *                   value;
            static const bool ref_count =    false;
        };
        typedef dependency_manager<dconfig>  assumption_manager;
        typedef assumption_manager::dependency * _assumption_set;
        typedef obj_ref<assumption_manager::dependency, assumption_manager> assumption_set_ref;
        

        typedef polynomial::cache cache;

        ctx&                    m_ctx;
        solver&                 m_solver;
        reslimit&               m_rlimit;
        small_object_allocator& m_allocator;
        bool                    m_incremental;
        unsynch_mpq_manager&    m_qm;
        pmanager&               m_pm;
        cache                   m_cache;
        anum_manager&           m_am;
        mutable assumption_manager     m_asm;
        assignment             m_assignment; // partial interpretation
        evaluator              m_evaluator;
        interval_set_manager & m_ism;
        ineq_atom_table        m_ineq_atoms;
        root_atom_table        m_root_atoms;
        svector<bool_var>      m_patch_var;
        polynomial_ref_vector  m_patch_num, m_patch_denom;
        
        id_gen                 m_cid_gen;
        clause_vector          m_clauses; // set of clauses
        clause_vector          m_learned; // set of learned clauses
        clause_vector          m_valids;

        unsigned               m_num_bool_vars;
        atom_vector            m_atoms;        // bool_var -> atom
        svector<lbool>         m_bvalues;      // boolean assignment
        unsigned_vector        m_levels;       // bool_var -> level
        svector<justification> m_justifications;
        // vector<clause_vector>  m_bwatches;     // bool_var (that are not attached to atoms) -> clauses where it is maximal
        bool_vector          m_dead;         // mark dead boolean variables
        id_gen                 m_bid_gen;

        bool_vector          m_is_int;     // m_is_int[x] is true if variable is integer
        // vector<clause_vector>  m_watches;    // var -> clauses where variable is maximal
        interval_set_vector    m_infeasible, m_frontend_infeasible; // var -> to a set of interval where the variable cannot be assigned to.
        atom_vector            m_var2eq;     // var -> to asserted equality
        var_vector             m_perm;       // var -> var permutation of the variables
        var_vector             m_inv_perm;

        // m_perm:     internal -> external
        // m_inv_perm: external -> internal
        struct perm_display_var_proc : public display_var_proc {
            var_vector &             m_perm;
            display_var_proc         m_default_display_var;
            display_var_proc const * m_proc; // display external var ids
            perm_display_var_proc(var_vector & perm):
                m_perm(perm),
                m_proc(nullptr) {
            }
            std::ostream& operator()(std::ostream & out, var x) const override {
                if (m_proc == nullptr)
                    m_default_display_var(out, x);
                else{
                    if(x == null_var){
                        out << " null var " << std::endl;
                    }
                    else{
                        (*m_proc)(out, m_perm[x]);
                    }
                }
                return out;
            }
        };
        perm_display_var_proc  m_display_var;

        display_assumption_proc const* m_display_assumption;
        struct display_literal_assumption : public display_assumption_proc {
            imp& i;
            literal_vector const& lits;
            display_literal_assumption(imp& i, literal_vector const& lits): i(i), lits(lits) {}
            std::ostream& operator()(std::ostream& out, assumption a) const override {
                if (lits.begin() <= a && a < lits.end()) {
                    out << *((literal const*)a);
                }
                else if (i.m_display_assumption) {
                    (*i.m_display_assumption)(out, a);
                }
                return out;
            }
        };
        struct scoped_display_assumptions {
            imp& i;
            display_assumption_proc const* m_save;
            scoped_display_assumptions(imp& i, display_assumption_proc const& p): i(i), m_save(i.m_display_assumption) {
                i.m_display_assumption = &p;
            }
            ~scoped_display_assumptions() {
                i.m_display_assumption = m_save;
            }
        };
        explain                m_explain;

        struct level {};
        struct stage {};
        struct semantics_decision {};
        struct bvar_assignment {};
        struct avar_assignment {};
        struct branch {};

        /**
            BVAR_ASSIGNMENT: assign literal (may be bool var)
            ARITH_ASSIGNMENT: assign arith var
            INFEASIBLE_UPDT: update infeasible information for arith var
            UPDT_EQ: update equation 
            SEMANTICS_DECISION: we face a conflict when processing arith var, use semantics decision to choose explain's literals
            BRANCH: decide next hybrid var
        */
        struct trail {
            enum kind { BVAR_ASSIGNMENT, ARITH_ASSIGNMENT, INFEASIBLE_UPDT, UPDT_EQ, NEW_LEVEL, NEW_STAGE, SEMANTICS_DECISION, BRANCH };
            kind               m_kind;
            hybrid_var         m_x, m_x2;

            union {
                interval_set * m_old_set;
                atom         * m_old_eq;
            };

            trail(bool_var x, bvar_assignment): m_kind(BVAR_ASSIGNMENT), m_x(x) {}
            trail(var x, avar_assignment): m_kind(ARITH_ASSIGNMENT), m_x(x) {}
            trail(level, bool_var b, var x): m_kind(NEW_LEVEL), m_x(b), m_x2(x) {}
            trail(stage): m_kind(NEW_STAGE) {}
            trail(var x, interval_set * old_set): m_kind(INFEASIBLE_UPDT), m_old_set(old_set), m_x{x} {}
            trail(var x, atom * a):m_kind(UPDT_EQ), m_old_eq(a), m_x(x) {}
            trail(var x, semantics_decision): m_kind(SEMANTICS_DECISION), m_x(x) {} 
            trail(var x, var y, branch): m_kind(BRANCH), m_x(x), m_x2(y) {}
        };
        svector<trail>         m_trail;

        class arith_level {
        public:
            var                m_arith;
            unsigned           m_level;

            arith_level(var _arith, unsigned _lvl): m_arith(_arith), m_level(_lvl) {}

            bool operator==(arith_level const &other) const {
                return m_arith == other.m_arith && m_level == other.m_level;
            }
            
            arith_level& operator=(arith_level const &other) {
                m_arith = other.m_arith;
                m_level = other.m_level;
                return *this;
            }
        };

        const arith_level default_arith_level = arith_level(null_var, null_var);

        anum                   m_zero;

        // configuration
        unsigned long long     m_max_memory;
        unsigned               m_lazy;  // how lazy the solver is: 0 - satisfy all learned clauses, 1 - process only unit and empty learned clauses, 2 - use only conflict clauses for resolving conflicts
        bool                   m_simplify_cores;
        bool                   m_reorder;
        bool                   m_randomize;
        bool                   m_random_order;
        unsigned               m_random_seed;
        bool                   m_inline_vars;
        bool                   m_log_lemmas;
        bool                   m_check_lemmas;
        unsigned               m_max_conflicts;
        unsigned               m_lemma_count;
        
        // statistics
        unsigned               m_conflicts;
        unsigned               m_decisions;
        unsigned               m_stages;
        unsigned               m_irrational_assignments; // number of irrational witnesses
        unsigned               m_unit_propagate, m_real_propagate;

        // vars
        unsigned               m_num_hybrid_vars;
        bool_var_vector        m_pure_bool_vars;
        bool_var_vector        m_pure_bool_convert;

        // atoms and clauses
        nlsat_atom_vector      m_nlsat_atoms;
        nlsat_clause_vector    m_nlsat_clauses;
        nlsat_learned_vector   m_nlsat_learned;

        // watchers
        vector<vector<atom_var_watcher *>>       m_var_watching_atoms;
        vector<vector<clause_var_watcher *>>     m_var_watching_clauses, m_var_watching_learned;
        vector<vector<clause_literal_watcher *>> m_pos_literal_watching_clauses, m_neg_literal_watching_clauses;
        vector<vector<clause_literal_watcher *>> m_pos_literal_watching_learned, m_neg_literal_watching_learned;
        
        // unit atom (static)
        vector<unsigned_vector>                  m_static_unit_atom;

        // unit atoms and clauses (dynamical)
        unsigned_vector                          m_atom_unit_clauses;
        unsigned_vector                          m_atom_unit_learned;
        vector<unsigned_vector>                  m_arith_unit_atom;
        vector<unsigned_vector>                  m_arith_unit_clauses;
        vector<unsigned_vector>                  m_arith_unit_clauses_more_lits;
        vector<unsigned_vector>                  m_arith_unit_learned;
        vector<unsigned_vector>                  m_arith_unit_learned_more_lits;

        // new generated unit clause or learned this propagation turn
        vector<unsigned_vector>                  m_newly_unit_arith_clauses;
        vector<unsigned_vector>                  m_newly_unit_arith_learned;

        // decisions
        bool_var_table                           m_decision_bools;
        // vsids
        double                                   arith_var_bump = 1;
        double                                   bool_var_bump = 1;
        double_vector                            m_hybrid_activity;
#if DYNAMIC_MODE == UNIFORM_VSIDS
        heap<uniform_vsids>               m_var_heap;
#elif DYNAMIC_MODE == BOOL_FIRST_VSIDS
        heap<bool_first_vsids>            m_var_heap;
#elif DYNAMIC_MODE == THEORY_FIRST_VSIDS
        heap<theory_first_vsids>          m_var_heap;
#elif DYNAMIC_MODE == ORIGIN_STATIC_BOOL_FIRST_MODE
        heap<static_bool_first_order>     m_var_heap;
#elif DYNAMIC_MODE == RANDOM_MODE
        heap<random_order>                m_var_heap;
#endif

        // restart
        unsigned               m_restart_conflicts;
        unsigned               m_restart_threshold;
        unsigned               m_restarts;
        unsigned               m_learned_added;
        unsigned               m_learned_deleted;

        // reduce
        double                 clause_bump = 1;
        double                 max_learnts;
        double                 m_reduce_threshold;
        unsigned               m_reduces;
        unsigned               m_reduce_conflicts;
        int                    learntsize_adjust_cnt;
        int                    learntsize_adjust_confl;

        // Trail recording assignment of literals (like in SAT Solver)
        /**
             \brief  a little difference from assigned literal
                    a literal can be valued without being assigned
            \example x + y <= 12
                    when x and y are assigned, this literal is valued but it may not be assigned according to decide or propagation
        */
        var_table              m_valued_atom_table;
        var_vector             m_valued_atom_trail;
        unsigned_vector        m_assigned_atom_indices;
        unsigned               m_atom_prop;
        // infeasible set
        var_vector             m_infeasible_var_trail;
        unsigned               m_infeasible_prop;

        // vars assignment trail
        bool_var_vector        m_bool_trail;
        var_vector             m_arith_trail;
        var_vector             m_hybrid_trail;
        unsigned_vector        m_hybrid_assigned_indices; // assigned order
        unsigned               m_arith_atom_prop; // arith var --> atom
        unsigned               m_hybrid_var_clause_prop, m_hybrid_var_learned_prop; // hybrid var --> clause / learned

        // var --> atom, clause, learned
        vector<var_vector>     m_var_atoms;
        vector<var_vector>     m_var_clauses;
        vector<var_vector>     m_var_learned;
        vector<var_vector>     m_bool_clauses;
        vector<var_vector>     m_bool_learned;

        using interval_set_bool = std::pair<bool, interval_set*>;
        // Cache for infeasible set computation
        vector<vector<interval_set_bool>>  m_var_atom_infeasible_set;
        vector<vector<interval_set_bool>>  m_var_clause_infeasible_set, m_var_learned_infeasible_set;

        // level and stage management
        hybrid_var             m_hk;
        unsigned               m_scope_lvl;
        unsigned               m_scope_stage;
        
        vector<arith_level>    m_arith_level;
        unsigned_vector        m_var_max_level;
        unsigned_vector        m_hybrid_find_stage;

        // conflict
        clause *               conflict_clause;
        bool                   frontend_conflict;
        var_table              m_conflict_arith, m_conflict_bool;
        
        // incremental datastruction generation
        bool                   generate_during_process;

        imp(solver &s, ctx &c) : m_ctx(c),
                                 m_solver(s),
                                 m_rlimit(c.m_rlimit),
                                 m_allocator(c.m_allocator),
                                 m_incremental(c.m_incremental),
                                 m_qm(c.m_qm),
                                 m_pm(c.m_pm),
                                 m_cache(m_pm),
                                 m_am(c.m_am),
                                 m_asm(*this, m_allocator),
                                 m_assignment(m_am),
                                 m_evaluator(s, m_assignment, m_pm, m_allocator),
                                 m_ism(m_evaluator.ism()),
                                 m_patch_num(m_pm),
                                 m_patch_denom(m_pm),
                                 m_num_bool_vars(0),
                                 m_display_var(m_perm),
                                 m_display_assumption(nullptr),
                                 m_explain(s, m_assignment, m_cache, m_atoms, m_var2eq, m_evaluator),
                                 m_scope_lvl(0),
                                 m_lemma(s),
                                 m_lazy_clause(s),
                                 m_lemma_assumptions(m_asm),

    #if DYNAMIC_MODE == UNIFORM_VSIDS
                                 m_var_heap(200, uniform_vsids(m_hybrid_activity))
    #elif DYNAMIC_MODE == BOOL_FIRST_VSIDS
                                 m_var_heap(200, bool_first_vsids(m_hybrid_activity, num_bool_vars()))
    #elif DYNAMIC_MODE == THEORY_FIRST_VSIDS
                                 m_var_heap(200, theory_first_vsids(m_hybrid_activity, num_bool_vars()))
    #elif DYNAMIC_MODE == ORIGIN_STATIC_BOOL_FIRST_MODE
                                 m_var_heap(200, static_bool_first_order(num_bool_vars()))
    #elif DYNAMIC_MODE == RANDOM_MODE
                                 m_var_heap(200, random_order(m_rand_seed))
    #endif

        {
            DTRACE(std::cout << "solver init" << std::endl;);
            clear();
            updt_params(c.m_params);
            reset_statistics();
            mk_true_bvar();
            m_lemma_count = 0;
            DTRACE(std::cout << "solver done" << std::endl;);
        }
        
        ~imp() {
            
        }

        void mk_true_bvar() {
            bool_var b = mk_bool_var();
            SASSERT(b == true_bool_var);
            literal true_lit(b, false);
            mk_clause(1, &true_lit, false, nullptr);
        }

        void updt_params(params_ref const & _p) {
            nlsat_params p(_p);
            m_max_memory     = p.max_memory();
            m_lazy           = p.lazy();
            m_simplify_cores = p.simplify_conflicts();
            bool min_cores   = p.minimize_conflicts();
            m_reorder        = p.reorder();
            m_randomize      = p.randomize();
            m_max_conflicts  = p.max_conflicts();
            m_random_order   = p.shuffle_vars();
            m_random_seed    = p.seed();
            m_inline_vars    = p.inline_vars();
            m_log_lemmas     = p.log_lemmas();
            m_check_lemmas   = p.check_lemmas();
            m_ism.set_seed(m_random_seed);
            m_explain.set_simplify_cores(m_simplify_cores);
            m_explain.set_minimize_cores(min_cores);
            m_explain.set_factor(p.factor());
            m_am.updt_params(p.p);
        }

        void reset() {
            m_explain.reset();
            m_lemma.reset();
            m_lazy_clause.reset();
            m_deleted_clauses.clear();
            undo_until_size(0);
            del_clauses();
            del_unref_atoms();
            m_cache.reset();
            m_assignment.reset();
            clear_nlsat_structures();
        }

        void clear() {
            m_explain.reset();
            m_lemma.reset();
            m_lazy_clause.reset();
            m_deleted_clauses.clear();
            undo_until_size(0);
            del_clauses();
            del_unref_atoms();
            clear_nlsat_structures();
        }

        void checkpoint() {
            if (!m_rlimit.inc()) {
                throw solver_exception(m_rlimit.get_cancel_msg()); 
            }
            if (memory::get_allocation_size() > m_max_memory) throw solver_exception(Z3_MAX_MEMORY_MSG);
        }

        // -----------------------
        //
        // Basic
        //
        // -----------------------
        unsigned num_arith_vars() const {
            return m_is_int.size();
        }

        unsigned num_bool_vars() const {
            return m_pure_bool_vars.size();
        }

        unsigned num_hybrid_vars() const {
            return m_num_hybrid_vars;
        }

        #define arith2hybrid(x)          (x == null_var ? null_var : x + num_bool_vars())
        #define hybrid2arith(x)          (x == null_var ? null_var : x - num_bool_vars())
        #define hybrid_is_bool(x)        (x < num_bool_vars())
        #define hybrid_is_arith(x)       (x >= num_bool_vars() && x != null_var)

        bool is_int(var x) const {
            return m_is_int[x];
        }

        void inc_ref(assumption) {}

        void dec_ref(assumption) {}

        void inc_ref(_assumption_set a) {
            if (a != nullptr) m_asm.inc_ref(a);
        }

        void dec_ref(_assumption_set a) {
            if (a != nullptr) m_asm.dec_ref(a);
        }

        void inc_ref(bool_var b) {
            if (b == null_bool_var)
                return;
            atom * a = m_atoms[b];
            if (a == nullptr)
                return;
            a->inc_ref();
        }
        
        void inc_ref(literal l) {
            inc_ref(l.var());
        }

        void dec_ref(bool_var b) {
            if (b == null_bool_var)
                return;
            atom * a = m_atoms[b];
            if (a == nullptr)
                return;
            SASSERT(a->ref_count() > 0);
            a->dec_ref();
            if (a->ref_count() == 0)
                del(a);
        }

        void dec_ref(literal l) {
            dec_ref(l.var());
        }

        bool is_arith_atom(bool_var b) const { return m_atoms[b] != nullptr; }

        bool is_arith_literal(literal l) const { return is_arith_atom(l.var()); }

        bool is_bool_literal(literal l) const { return m_atoms[l.var()] == nullptr; }

        static inline double drand(unsigned seed){
            random_gen r(++seed);
            return r() / (1.0 * r.max_value());
        }

        bool_var mk_bool_var_core() {
            bool_var b = m_bid_gen.mk();
            m_num_bool_vars++;
            m_atoms         .enlarge(b, nullptr);
            m_bvalues       .enlarge(b, l_undef);
            m_levels        .setx(b, UINT_MAX, UINT_MAX);
            m_arith_level   .setx(b, default_arith_level, default_arith_level);
            m_justifications.setx(b, null_justification, null_justification);
            m_dead          .setx(b, false, true);
            return b;
        }

        /**
         \brief Create a fresh boolean variable that is not associated with any
          nonlinear arithmetic atom.
        */
        bool_var mk_bool_var() {
            return mk_bool_var_core();
        }

        var mk_var(bool is_int) {
            var x = m_pm.mk_var();
            register_var(x, is_int);
            return x;
        }

        void register_var(var x, bool is_int) {
            SASSERT(x == num_arith_vars());
            m_is_int.    push_back(is_int);
            m_infeasible.push_back(0);
            m_var2eq.    push_back(nullptr);
            m_perm.      push_back(x);
            m_inv_perm.  push_back(x);
            m_var_max_level.push_back(0);
            SASSERT(m_is_int.size() == m_infeasible.size());
            SASSERT(m_is_int.size() == m_var2eq.size());
            SASSERT(m_is_int.size() == m_perm.size());
            SASSERT(m_is_int.size() == m_inv_perm.size());
            SASSERT(m_var_max_level.size() == m_is_int.size());
        }

        bool_vector m_found_vars;
        void vars(literal l, var_vector& vs) {                
            vs.reset();
            atom * a = m_atoms[l.var()];
            if (a == nullptr) {
                
            }
            else if (a->is_ineq_atom()) {
                unsigned sz = to_ineq_atom(a)->size();
                var_vector new_vs;
                for (unsigned j = 0; j < sz; j++) {
                    m_found_vars.reset();
                    m_pm.vars(to_ineq_atom(a)->p(j), new_vs);
                    for (unsigned i = 0; i < new_vs.size(); ++i) {
                        if (!m_found_vars.get(new_vs[i], false)) {
                            m_found_vars.setx(new_vs[i], true, false);
                            vs.push_back(new_vs[i]);
                        }
                    }
                }
            }
            else {
                m_pm.vars(to_root_atom(a)->p(), vs);
                if(!vs.contains(to_root_atom(a)->x())) {
                    vs.push_back(to_root_atom(a)->x());
                }
            }
        }

        void deallocate(ineq_atom * a) {
            unsigned obj_sz = ineq_atom::get_obj_size(a->size());
            a->~ineq_atom();
            m_allocator.deallocate(obj_sz, a);
        }

        void deallocate(root_atom * a) {
            a->~root_atom();
            m_allocator.deallocate(sizeof(root_atom), a);
        }

        void del(bool_var b) {
            m_num_bool_vars--;
            m_dead[b]  = true;
            m_atoms[b] = nullptr;
            m_bvalues[b] = l_undef;
            m_bid_gen.recycle(b);
            del_nlsat_atom(b);
        }

        void del(ineq_atom * a) {
            m_ineq_atoms.erase(a);
            del(a->bvar());
            unsigned sz = a->size();
            for (unsigned i = 0; i < sz; i++)
                m_pm.dec_ref(a->p(i));
            deallocate(a);
        }

        void del(root_atom * a) {
            SASSERT(a->ref_count() == 0);
            m_root_atoms.erase(a);
            del(a->bvar());
            m_pm.dec_ref(a->p());
            deallocate(a);
        }

        void del(atom * a) {
            if (a == nullptr)
                return;
            if (a->is_ineq_atom())
                del(to_ineq_atom(a));
            else
                del(to_root_atom(a));
        }
        
        // Delete atoms with ref_count == 0
        void del_unref_atoms() {
            for (auto* a : m_atoms) {
                del(a);
            }
        }

        ineq_atom* mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even, bool& is_new) {
            SASSERT(sz >= 1);
            SASSERT(k == atom::LT || k == atom::GT || k == atom::EQ);
            int sign = 1;
            polynomial_ref p(m_pm);
            ptr_buffer<poly> uniq_ps;
            for (unsigned i = 0; i < sz; i++) {
                p = m_pm.flip_sign_if_lm_neg(ps[i]);
                if (p.get() != ps[i] && !is_even[i]) {
                    sign = -sign;
                }
                uniq_ps.push_back(m_cache.mk_unique(p));
            }
            void * mem = m_allocator.allocate(ineq_atom::get_obj_size(sz));
            if (sign < 0)
                k = atom::flip(k);
            ineq_atom * tmp_atom = new (mem) ineq_atom(k, sz, uniq_ps.data(), is_even);
            ineq_atom * atom = m_ineq_atoms.insert_if_not_there(tmp_atom);
            is_new = (atom == tmp_atom);
            if (is_new) {
                for (unsigned i = 0; i < sz; i++) {
                    m_pm.inc_ref(atom->p(i));
                }
            }
            else {
                deallocate(tmp_atom);
            }
            return atom;
        }

        bool_var mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even) {
            bool is_new = false;
            ineq_atom* atom = mk_ineq_atom(k, sz, ps, is_even, is_new);
            if (!is_new) {
                return atom->bvar();
            }
            else {
                bool_var b = mk_bool_var_core();
                m_atoms[b] = atom;
                atom->m_bool_var = b;
                if(generate_during_process) {
                    register_nlsat_atom(b);
                }
                return b;
            }
        }

        literal mk_ineq_literal(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even) {
            SASSERT(k == atom::LT || k == atom::GT || k == atom::EQ);
            bool is_const = true;
            polynomial::manager::scoped_numeral cnst(m_pm.m());
            m_pm.m().set(cnst, 1);            
            for (unsigned i = 0; i < sz; ++i) {
                if (m_pm.is_const(ps[i])) {
                    if (m_pm.is_zero(ps[i])) {
                        m_pm.m().set(cnst, 0);
                        is_const = true;
                        break;
                    }
                    auto const& c = m_pm.coeff(ps[i], 0);
                    m_pm.m().mul(cnst, c, cnst);
                    if (is_even[i] && m_pm.m().is_neg(c)) {
                        m_pm.m().neg(cnst);
                    }                            
                }
                else {
                    is_const = false;
                }
            }
            if (is_const) {
                if (m_pm.m().is_pos(cnst) && k == atom::GT) return true_literal;
                if (m_pm.m().is_neg(cnst) && k == atom::LT) return true_literal;
                if (m_pm.m().is_zero(cnst) && k == atom::EQ) return true_literal;
                return false_literal;
            }
            literal res = literal(mk_ineq_atom(k, sz, ps, is_even), false);
            std::cout << "we are here" << std::endl;
            std::cout << m_nlsat_atoms[res.var()]->m_var_watcher->v1 << " ";
            std::cout << m_nlsat_atoms[res.var()]->m_var_watcher->v2 << std::endl;
            return res;
        }

        bool_var mk_root_atom(atom::kind k, var x, unsigned i, poly * p) {
            polynomial_ref p1(m_pm), uniq_p(m_pm);
            p1 = m_pm.flip_sign_if_lm_neg(p); // flipping the sign of the polynomial will not change its roots.
            uniq_p = m_cache.mk_unique(p1); 
            SASSERT(i > 0);
            SASSERT(k == atom::ROOT_LT || k == atom::ROOT_GT || k == atom::ROOT_EQ || k == atom::ROOT_LE || k == atom::ROOT_GE);
            void * mem = m_allocator.allocate(sizeof(root_atom));
            root_atom * new_atom = new (mem) root_atom(k, x, i, uniq_p);
            root_atom * old_atom = m_root_atoms.insert_if_not_there(new_atom);
            if (old_atom != new_atom) {
                deallocate(new_atom);
                return old_atom->bvar();
            }
            bool_var b = mk_bool_var_core();
            m_atoms[b] = new_atom;
            new_atom->m_bool_var = b;
            m_pm.inc_ref(new_atom->p());
            if(generate_during_process) {
                register_nlsat_atom(b);
            }
            return b;
        }

        bool is_bool_clause(clause const & cls) const {
            for(unsigned i = 0; i < cls.size(); i++){
                literal l = cls[i];
                if(is_arith_literal(l)){
                    return false;
                }
            }
            return true;
        }

        void deallocate(clause * cls) {
            size_t obj_sz = clause::get_obj_size(cls->size());
            cls->~clause();
            m_allocator.deallocate(obj_sz, cls);
        }

        unsigned_vector        m_deleted_clauses;
        
        void del_clause(clause * cls) {
            DTRACE(std::cout << "delete clause: ";
                display(std::cout, cls) << std::endl;
            );
            m_deleted_clauses.push_back(cls->id());
            if(cls->is_learned()) {
                del_nlsat_learned(cls->id());
            } else {
                del_nlsat_clause(cls->id());
            }
            m_cid_gen.recycle(cls->id());
            unsigned sz = cls->size();
            for (unsigned i = 0; i < sz; i++)
                dec_ref((*cls)[i]);
            _assumption_set a = static_cast<_assumption_set>(cls->assumptions());
            dec_ref(a);
            deallocate(cls);
        }

        void del_clause(clause * cls, clause_vector& clauses) {
            clauses.erase(cls);
            del_clause(cls);
        }

        void del_clauses(ptr_vector<clause> & cs) {
            for (clause* cp : cs) 
                del_clause(cp);
            cs.reset();
        }

        void del_clauses() {
            del_clauses(m_clauses);
            del_clauses(m_learned);
            del_clauses(m_valids);
        }

        // We use a simple heuristic to sort literals
        //   - bool literals < arith literals
        //   - sort literals based on max_var
        //   - sort literal with the same max_var using degree
        //     break ties using the fact that ineqs are usually cheaper to process than eqs.
        struct lit_lt {
            imp & m;
            lit_lt(imp & _m):m(_m) {}

            bool operator()(literal l1, literal l2) const {
                atom * a1 = m.m_atoms[l1.var()];
                atom * a2 = m.m_atoms[l2.var()];
                if (a1 == nullptr && a2 == nullptr)
                    return l1.index() < l2.index();
                if (a1 == nullptr)
                    return true;
                if (a2 == nullptr)
                    return false;
                var x1 = m.max_stage_literal(l1);
                var x2 = m.max_stage_literal(l2);
                if (x1 < x2)
                    return true;
                if (x1 > x2)
                    return false;
                SASSERT(x1 == x2);
                unsigned d1 = m.max_degree_of_stage_var(a1);
                unsigned d2 = m.max_degree_of_stage_var(a2);
                if (d1 < d2)
                    return true;
                if (d1 > d2)
                    return false;
                if (!a1->is_eq() && a2->is_eq())
                    return true;
                if (a1->is_eq() && !a2->is_eq())
                    return false;
                return l1.index() < l2.index();
            }
        };

        class scoped_bool_vars { 
            imp& s;
            svector<bool_var> vec;
        public:
            scoped_bool_vars(imp& s):s(s) {}
            ~scoped_bool_vars() {
                for (bool_var v : vec) {
                    s.dec_ref(v);
                }
            }
            void push_back(bool_var v) {
                s.inc_ref(v);
                vec.push_back(v);
            }
            bool_var const* begin() const { return vec.begin(); }
            bool_var const* end() const { return vec.end(); }
            bool_var operator[](bool_var v) const { return vec[v]; }
        };

        void check_lemma(unsigned n, literal const* cls, bool is_valid, assumption_set a) {
            IF_VERBOSE(0, display(verbose_stream() << "check lemma: ", n, cls) << "\n");
            for (clause* c : m_learned) IF_VERBOSE(1, display(verbose_stream() << "lemma: ", *c) << "\n"); 
            
            solver solver2(m_ctx);
            imp& checker = *(solver2.m_imp);
            checker.m_check_lemmas = false;
            checker.m_log_lemmas = false;
            checker.m_inline_vars = false;

            // need to translate Boolean variables and literals
            scoped_bool_vars tr(checker);
            for (var x = 0; x < m_is_int.size(); ++x) {
                checker.register_var(x, m_is_int[x]);
            }
            bool_var bv = 0;
            tr.push_back(bv);
            for (bool_var b = 1; b < m_atoms.size(); ++b) {
                atom* a = m_atoms[b];
                if (a == nullptr) {
                    bv = checker.mk_bool_var();
                }
                else if (a->is_ineq_atom()) {
                    ineq_atom& ia = *to_ineq_atom(a);
                    unsigned sz = ia.size();
                    ptr_vector<poly> ps;
                    bool_vector is_even;
                    for (unsigned i = 0; i < sz; ++i) {
                        ps.push_back(ia.p(i));
                        is_even.push_back(ia.is_even(i));
                    }
                    bv = checker.mk_ineq_atom(ia.get_kind(), sz, ps.data(), is_even.data());
                }
                else if (a->is_root_atom()) {
                    root_atom& r = *to_root_atom(a);
                    bv = checker.mk_root_atom(r.get_kind(), r.x(), r.i(), r.p());
                }
                else {
                    UNREACHABLE();
                }
                tr.push_back(bv);
            }
            if (!is_valid) {
                for (clause* c : m_clauses) {
                    if (!a && c->assumptions()) {
                        continue;
                    }
                    literal_vector lits;
                    for (literal lit : *c) {
                        lits.push_back(literal(tr[lit.var()], lit.sign()));
                    }
                    checker.mk_clause(lits.size(), lits.data(), nullptr);
                }
            }
            for (unsigned i = 0; i < n; ++i) {
                literal lit = cls[i];
                literal nlit(tr[lit.var()], !lit.sign());
                checker.mk_clause(1, &nlit, nullptr);
            }
            IF_VERBOSE(0, verbose_stream() << "check\n";);
            lbool r = checker.check();
            if (r == l_true) {
                for (bool_var b : tr) {
                    literal lit(b, false);
                    IF_VERBOSE(0, checker.display(verbose_stream(), lit) << " := " << checker.value(lit) << "\n");
                }
                for (clause* c : m_learned) {
                    bool found = false;
                    for (literal lit: *c) {
                        literal tlit(tr[lit.var()], lit.sign());
                        found |= checker.value(tlit) == l_true;
                    }
                    if (!found) {
                        IF_VERBOSE(0, display(verbose_stream() << "violdated clause: ", *c) << "\n");
                    }
                }
                for (clause* c : m_valids) {
                    bool found = false;
                    for (literal lit: *c) {
                        literal tlit(tr[lit.var()], lit.sign());
                        found |= checker.value(tlit) == l_true;
                    }
                    if (!found) {
                        IF_VERBOSE(0, display(verbose_stream() << "violdated tautology clause: ", *c) << "\n");
                    }                    
                }
                UNREACHABLE();
            }
        }

        void log_lemma(std::ostream& out, clause const& cls) {
            display_smt2(out);
            out << "(assert (not ";
            display_smt2(out, cls) << "))\n";
            display(out << "(echo \"#" << m_lemma_count << " ", cls) << "\")\n";
            out << "(check-sat)\n(reset)\n";
        }

        clause * mk_clause_core(unsigned num_lits, literal const * lits, bool learned, _assumption_set a) {
            SASSERT(num_lits > 0);
            unsigned cid = m_cid_gen.mk();
            void * mem = m_allocator.allocate(clause::get_obj_size(num_lits));
            clause * cls = new (mem) clause(cid, num_lits, lits, learned, a);
            for (unsigned i = 0; i < num_lits; i++)
                inc_ref(lits[i]);
            inc_ref(a);
            return cls;
        }

        clause * mk_clause(unsigned num_lits, literal const * lits, bool learned, _assumption_set a) {
            SASSERT(num_lits > 0);
            clause * cls = mk_clause_core(num_lits, lits, learned, a);
            ++m_lemma_count;
            if (learned && m_log_lemmas) {
                log_lemma(verbose_stream(), *cls);
            }
            if (learned && m_check_lemmas) {
                check_lemma(cls->size(), cls->data(), false, cls->assumptions());
            }
            if (learned){
                m_learned.push_back(cls);
                m_learned_added++;
                register_nlsat_learned(m_learned.size() - 1);
                clause_bump_act(*cls);
            }
            else{
                m_clauses.push_back(cls);
                SASSERT(m_clauses.size() == m_clause_vars.size());
            }
            return cls;
        }
        
        void bump_conflict_hybrid_vars() {
            for(var v: m_conflict_arith){
                arith_bump_act(v);
            }
            for(bool_var b: m_conflict_bool){
                bool_var_bump_act(b);
            }
        }

        void arith_bump_act(var v){
            arith_bump_act(v, arith_var_bump);
        }

        void bool_var_bump_act(bool_var b){
            bool_var_bump_act(b, bool_var_bump);
        }

        void arith_bump_act(var v, double inc){
            v = v + num_bool_vars();
            if((m_hybrid_activity[v] += inc) > 1e100){
                // smooth
                for(hybrid_var i = num_bool_vars(); i < m_num_hybrid_vars; i++){
                    m_hybrid_activity[i] *= 1e-100;
                }
                arith_var_bump *= 1e-100;
            }
            if(m_var_heap.contains(v)){
                m_var_heap.decreased(v);
            }
        }

        void bool_var_bump_act(bool_var b, double inc){
            if((m_hybrid_activity[b] += inc) > 1e100){
                // smooth
                for(hybrid_var i = 0; i < num_bool_vars(); i++){
                    m_hybrid_activity[i] *= 1e-100;
                }
                bool_var_bump *= 1e-100;
            }
            if(m_var_heap.contains(b)){
                m_var_heap.decreased(b);
            }
        }

        void clause_bump_act(clause &cls) {
            clause_bump_act(cls, clause_bump);
        }

        void clause_bump_act(clause & cls, double inc){
            SASSERT(cls.is_learned());
            cls.set_activity(cls.get_activity() + inc);
            if(cls.get_activity() > 1e20){ // smooth activity
                for(unsigned j = 0; j < m_learned.size(); j++){ // smooth
                    m_learned[j]->set_activity(m_learned[j]->get_activity() * 1e-20);
                }
                clause_bump *= 1e-20;
            }
        }

        void get_learned_last_assigned_one_hybrid_var(unsigned idx, hybrid_var &v) const {
            unsigned max_i = null_var;
            for(bool_var b: m_nlsat_learned[idx]->m_bool_vars) {
                unsigned index = m_hybrid_assigned_indices[b];
                if(index == null_var) {
                    continue;
                }
                if(max_i == null_var) {
                    max_i = index;
                    v = b;
                } else if(index > max_i) {
                    max_i = index;
                    v = b;
                }
            }
            for(var x: m_nlsat_learned[idx]->m_arith_vars) {
                hybrid_var b = hybrid2arith(x);
                unsigned index = m_hybrid_assigned_indices[b];
                if(index == null_var) {
                    continue;
                }
                if(max_i == null_var) {
                    max_i = index;
                    v = b;
                } else if(index > max_i) {
                    max_i = index;
                    v = b;
                }
            }
        }

        void get_learned_last_assigned_two_hybrid_vars(unsigned idx, hybrid_var &v1, hybrid_var &v2) const {
            unsigned max1 = null_var, max2 = null_var;
            for(bool_var b: m_nlsat_learned[idx]->m_bool_vars) {
                unsigned index = m_hybrid_assigned_indices[b];
                if(index == null_var) {
                    continue;
                }
                if(max1 == null_var) {
                    max1 = index;
                    v1 = b;
                } else if(max2 == null_var) {
                    if(index >= max1) {
                        max2 = max1;
                        v2 = v1;
                        max1 = index;
                        v1 = b;
                    } else {
                        max2 = index;
                        v2 = b;
                    }
                } else {
                    if(index >= max1) {
                        max2 = max1;
                        v2 = v1;
                        max1 = index;
                        v1 = b;
                    } else if(index >= max2 && index < max1) {
                        max2 = index;
                        v2 = b;
                    } else {

                    }
                }
            }
            for(var v: m_nlsat_learned[idx]->m_arith_vars) {
                hybrid_var b = arith2hybrid(v);
                unsigned index = m_hybrid_assigned_indices[b];
                if(index == null_var) {
                    continue;
                }
                if(max1 == null_var) {
                    max1 = index;
                    v1 = b;
                } else if(max2 == null_var) {
                    if(index >= max1) {
                        max2 = max1;
                        v2 = v1;
                        max1 = index;
                        v1 = b;
                    } else {
                        max2 = index;
                        v2 = b;
                    }
                } else {
                    if(index >= max1) {
                        max2 = max1;
                        v2 = v1;
                        max1 = index;
                        v1 = b;
                    } else if(index >= max2 && index < max1) {
                        max2 = index;
                        v2 = b;
                    } else {

                    }
                }
            }
        }

        void set_learned_var_watcher(unsigned idx) {
            nlsat_learned const *cls = m_nlsat_learned[idx];
            clause_var_watcher *new_watcher;
            type_var_table m_vars;
            for(bool_var b: cls->m_bool_vars) {
                m_vars.insert(type_var(b, true));
            }
            for(var v: cls->m_arith_vars) {
                m_vars.insert(type_var(v, false));
            }
            if(m_vars.size() == 1) { // unit clause
                hybrid_var v = type2hybrid(*m_vars.begin());
                if(hybrid_is_bool(v)) { 
                    // we do nothing, since this will be assigned by up
                } else {
                    var av = hybrid2arith(v);
                    if(OPTIONS::learned_arith_frontend) {
                        if(!update_learned_frontend_infeasible_set(idx, av)) {
                            frontend_conflict = true;
                            return;
                        } else {
                            if(m_learned[idx]->is_unit()) {
                                frontend_propagate((*m_learned[idx])[0], idx, true, true);
                            }
                        }
                    }
                    if(!m_assignment.is_assigned(av)) {
                        m_arith_unit_learned[av].push_back(idx);
                        m_newly_unit_arith_learned[av].push_back(idx);
                        if(m_learned[idx]->size() >= 2) {
                            m_arith_unit_learned_more_lits[av].push_back(idx);
                        }
                    }
                }
            } else { // vars >= 2
                hybrid_var v1 = null_var, v2 = null_var;
                for(auto const &tv: m_vars) {
                    if(!type_var_assigned(tv)) {
                        if(v1 == null_var) {
                            v1 = type2hybrid(tv);
                        } else if(v2 == null_var) {
                            v2 = type2hybrid(tv);
                        }
                    }
                }
                if(v1 != null_var && v2 != null_var) { // two unassigned
                    // do nothing
                } else if(v1 != null_var && v2 == null_var) { // one unassigned
                    get_learned_last_assigned_one_hybrid_var(idx, v2);
                } else { // all assigned
                    get_learned_last_assigned_two_hybrid_vars(idx, v1, v2);
                }
                new_watcher = new clause_var_watcher(idx, v1, v2);
                m_var_watching_learned[v1].push_back(new_watcher);
                m_var_watching_learned[v2].push_back(new_watcher);
                m_nlsat_learned[idx]->m_var_watcher = new_watcher;
                if(hybrid_var_assigned(v1) && !hybrid_var_assigned(v2)) { // unit to v2
                    if(hybrid_is_arith(v2)) {
                        var av = hybrid2arith(v2);
                        m_arith_unit_learned[av].push_back(idx);
                        m_newly_unit_arith_learned[av].push_back(idx);
                        if(m_learned[idx]->size() >= 2) {
                            m_arith_unit_learned_more_lits[av].push_back(idx);
                        }
                    }
                } else if(!hybrid_var_assigned(v1) && hybrid_var_assigned(v2)) { // unit to v1
                    if(hybrid_is_arith(v1)) {
                        var av = hybrid2arith(v1);
                        m_arith_unit_learned[av].push_back(idx);
                        m_newly_unit_arith_learned[av].push_back(idx);
                        if(m_learned[idx]->size() >= 2) {
                            m_arith_unit_learned_more_lits[av].push_back(idx);
                        }
                        if (!update_learned_infeasible_set(idx, av)) {
                            conflict_clause = m_learned[idx];
                            return;
                        } else {
                            if(m_learned[idx]->size() == 1) {
                                assign_literal((*m_learned[idx])[0], mk_clause_jst(m_learned[idx]));
                            }
                        }
                    }
                }
            }
        }

        void get_learned_last_assigned_two_literal_indices(unsigned idx, unsigned &id1, unsigned &id2) {
            unsigned max1 = null_var, max2 = null_var;
            for(int i = 0; i < m_learned[idx]->size(); i++) {
                literal l = (*m_learned[idx])[i];
                unsigned index = m_assigned_atom_indices[l.var()];
                if(index == null_var) {
                    continue;
                }
                if(max1 == null_var) {
                    max1 = index;
                    id1 = i;
                } else if(max2 == null_var) {
                    if(index >= max1) {
                        max2 = max1;
                        id2 = id1;
                        max1 = index;
                        id1 = i;
                    } else {
                        max2 = index;
                        id2 = i;
                    }
                } else {
                    if(index >= max1) { // largest
                        max2 = max1;
                        id2 = id1;
                        max1 = index;
                        id1 = i;
                    } else if(index >= max2 && index < max1) { // second largest
                        max2 = index;
                        id2 = i;
                    } else {
                        // do nothing
                    }
                }
            }
        }

        void get_learned_last_assigned_one_literal_indices(unsigned idx, unsigned &id) {
            unsigned max_i = null_var;
            for(int i = 0; i < m_learned[idx]->size(); i++) {
                literal l = (*m_learned[idx])[i];
                unsigned index = m_assigned_atom_indices[l.var()];
                if(index == null_var) {
                    continue;
                }
                if(max_i == null_var) {
                    max_i = index;
                    id = i;
                } else if(index > max_i) {
                    max_i = index;
                    id = i;
                }
            }
        }

        /**
         \brief Set Literal Watcher for learned clauses
        */
        void set_learned_literal_watcher(unsigned idx) {
            clause const &curr_clause = *m_learned[idx];
            SASSERT(curr_clause.size() > 0);
            if(curr_clause.size() == 1) { // unit clause
                literal l = curr_clause[0];
                if(OPTIONS::learned_literal_frontend) {
                    if (frontend_value(l) == l_false) {
                        frontend_conflict = true;
                        return;
                    }
                    frontend_propagate(l, idx, true, is_bool_literal(l));
                }
                m_atom_unit_learned[l.var()] = idx;
                if(value(l) == l_false) {
                    conflict_clause = m_learned[idx];
                    return;
                }
                if(is_bool_literal(l)) {
                    assign_literal(l, mk_clause_jst(&curr_clause));
                }
            } else { // more literals
                bool is_sat = false; unsigned id1 = null_var, id2 = null_var;
                for(int idx2 = 0; idx2 < curr_clause.size(); idx2++) {
                    literal l = curr_clause[idx2];
                    if(value(l) == l_true) {
                        is_sat = true;
                        continue;
                    }
                    if(value(l) == l_false) {
                        continue;
                    }
                    if(id1 == null_var) {
                        id1 = idx2;
                    } else if(id2 == null_var) {
                        id2 = idx2;
                    }
                }
                if(id1 == null_var && id2 == null_var) { // conflict
                    conflict_clause = is_sat ? nullptr : m_learned[idx];
                    get_learned_last_assigned_two_literal_indices(idx, id1, id2);
                }
                else if(id1 != null_var && id2 == null_var) { // one unassigned clause
                    if(is_bool_literal(curr_clause[id1])) {
                        assign_literal(curr_clause[id1], mk_clause_jst(&curr_clause));
                    }
                    get_learned_last_assigned_one_literal_indices(idx, id2);
                } else if(id1 != null_var && id2 != null_var) { // two unassigned
                    // do nothing
                }
                literal l1 = curr_clause[id1], l2 = curr_clause[id2];
                int i1 = l1.sign() ? -l1.var() : l1.var();
                int i2 = l2.sign() ? -l2.var() : l2.var();
                SASSERT(i1 != 0 && i2 != 0);
                clause_literal_watcher *new_watcher = new clause_literal_watcher(idx, i1, i2);
                if(!l1.sign()) {
                    m_pos_literal_watching_learned[l1.var()].push_back(new_watcher);
                } else {
                    m_neg_literal_watching_learned[l1.var()].push_back(new_watcher);
                }
                if(!l2.sign()) {
                    m_pos_literal_watching_learned[l2.var()].push_back(new_watcher);
                } else {
                    m_neg_literal_watching_learned[l2.var()].push_back(new_watcher);
                }
                m_nlsat_learned[idx]->m_atom_watcher = new_watcher;
            }
        }

        inline hybrid_var type2hybrid(type_var const &tv) const {
            return tv.is_bool ? tv.v : tv.v + num_bool_vars();
        }

        bool type_var_assigned(type_var const& tv) const {
            return tv.is_bool ? m_bvalues[m_pure_bool_vars[tv.v]] != l_undef : m_assignment.is_assigned(tv.v);
        }

        bool hybrid_var_assigned(hybrid_var v) const {
            return v >= num_bool_vars() ? m_assignment.is_assigned(v - num_bool_vars()) : m_bvalues[m_pure_bool_vars[v]] != l_undef;
        }

        void mk_clause(unsigned num_lits, literal const * lits, assumption a) {
            _assumption_set as = nullptr;
            if (a != nullptr)
                as = m_asm.mk_leaf(a);
            if (num_lits == 0) {
                num_lits = 1;
                lits = &false_literal;
            }
            mk_clause(num_lits, lits, false, as);
        }

        void save_bool_assign_trail(bool_var b) {
            m_trail.push_back(trail(b, bvar_assignment()));
        }

        void save_arith_assignment_trail(var v){
            m_trail.push_back(trail(v, avar_assignment()));
        }

        void save_set_updt_trail(var x, interval_set * old_set) {
            m_trail.push_back(trail(x, old_set));
            m_infeasible_var_trail.push_back(x);
        }

        void save_semantics_decision_trail(var v) {
            m_trail.push_back(trail(v, semantics_decision()));
        }

        void save_updt_eq_trail(var x, atom * old_eq) {
            m_trail.push_back(trail(x, old_eq));
        }

        void save_new_stage_trail() {
            m_trail.push_back(trail(stage()));
        }

        void save_new_level_trail(bool_var b, var v) {
            m_trail.push_back(trail(level(), b, v));
        }

        void save_branch_trail(var old_v, var new_v) {
            m_trail.push_back(trail(old_v, new_v, branch()));
        }
    
        /**
          \brief When x is unassigned, update unit clauses
          \note We only need to erase clauses and atoms that are watched by x
        */
        void update_unit_after_var_unassigned(hybrid_var x) {
            if(hybrid_is_arith(x)) {
                update_unit_atom_after_var_unassigned(hybrid2arith(x));
            }
            update_unit_clause_after_var_unassigned(x);
            update_unit_learned_after_var_unassigned(x);
        }

        /**
          \brief We only need to update those atoms watched by var x
          \note Proof: assume an atom <a> not watched by x turns unit after unassigning var <x>
                       then <a> must contain var <x>
                       \case 1: <a> is unit, then it must be watched by x
                       \case 2: <a> is binary, same to case 1
                       \case 3: <a> contains more vars and is watched by <y, z>.
                                \case 3.1: x -> (y or z), then unassigning x will cause two or more unassigned vars
                                \case 3.2 (y or z) -> x, then when (y or z) is assigned, algorithm will update (y or z) to x

            sublemma: if a clause is watched by <x, y>, x and y are unassigned or most recent assigned
        */
        void update_unit_atom_after_var_unassigned(var x) {
            SASSERT(m_arith_unit_atom[x].empty());
            for(int i = 0; i < m_var_watching_atoms[x].size(); i++) {
                atom_var_watcher *watcher = m_var_watching_atoms[x][i];
                var another_var = watcher->get_another_var(x);
                int idx = watcher->m_atom_index;
                if(another_var == null_var || m_assignment.is_assigned(another_var)) { // previously all assigned
                    if(m_atoms[idx]->is_ineq_atom() || to_root_atom(m_atoms[idx])->x() == x) {
                        insert_unit_atom(idx, x);
                    }
                } else { // another var is unassigned, currently x is also unassigned
                    m_arith_unit_atom[another_var].erase(idx);
                }
            }
            for(auto idx: m_static_unit_atom[x]) {
                insert_unit_atom(idx, x);
            }
        }
        
        /**
          \brief Record unit atom for given var
          Propagate atom using current infeasible set.
        */
        void insert_unit_atom(unsigned idx, var x) {
            DTRACE(std::cout << "insert unit atom: "; display_atom(std::cout, idx) << std::endl;);
            m_arith_unit_atom[x].push_back(idx);
            propagate_atom(idx, x);
            DTRACE(std::cout << "insert unit atom done " << std::endl;);
        }

        void update_unit_clause_after_var_unassigned(hybrid_var x) {
            for(int i = 0; i < m_var_watching_clauses[x].size(); i++) {
                clause_var_watcher *watcher = m_var_watching_clauses[x][i];
                var another_var = watcher->get_another_var(x);
                int idx = watcher->m_clause_index;
                if(another_var == null_var || is_hybrid_assigned(another_var)) { // previously all assigned
                    if(hybrid_is_arith(x)) {
                        var v = hybrid2arith(x);
                        m_arith_unit_clauses[v].insert(idx);
                        m_newly_unit_arith_clauses[v].push_back(idx);
                        if(m_clauses[idx]->size() > 1) {
                            m_arith_unit_clauses_more_lits[v].insert(idx);
                        }
                    }
                } else { // another var is unassigned, currently x is also unassigned
                    if(hybrid_is_arith(another_var)) {
                        var v = hybrid2arith(another_var);
                        m_arith_unit_clauses[v].erase(idx);
                        m_arith_unit_clauses_more_lits[v].erase(idx);
                        m_newly_unit_arith_clauses[v].erase(idx);
                    }
                }
            }
        }

        /**
          \brief Update real unit learned clauses after an arith var is unassigned
        */
        void update_unit_learned_after_var_unassigned(hybrid_var x) {
            for(int i = 0; i < m_var_watching_learned[x].size(); i++) {
                clause_var_watcher *watcher = m_var_watching_learned[x][i];
                var another_var = watcher->get_another_var(x);
                int idx = watcher->m_clause_index;
                if(another_var == null_var || m_assignment.is_assigned(another_var)) { // previously all assigned
                    if(hybrid_is_arith(x)) {
                        var v = hybrid2arith(x);
                        if(check_learned_unit(idx, v)) {
                            m_arith_unit_learned[v].insert(idx);
                            m_newly_unit_arith_learned[v].push_back(idx);
                            if(m_learned[idx]->size() > 1) {
                                m_arith_unit_learned_more_lits[v].insert(idx);
                            }
                        }
                    }
                } else {
                    if(hybrid_is_arith(another_var)) {
                        var v = hybrid2arith(another_var);
                        m_arith_unit_learned[v].erase(idx);
                        m_newly_unit_arith_learned[v].erase(idx);
                        m_arith_unit_learned_more_lits[v].erase(idx);
                    }
                }
            }
        }

        void undo_avar_assignment(var x){
            DTRACE(std::cout << "undo avar assignment" << std::endl;);
            hybrid_var hv = arith2hybrid(x);
            m_assignment.reset(x);
            m_hybrid_assigned_indices[hv] = null_var;
            m_hybrid_trail.pop_back();
            m_arith_trail.pop_back();
            m_arith_atom_prop--;
            m_hybrid_var_clause_prop--;
            m_hybrid_var_learned_prop--;
            update_unit_after_var_unassigned(hv);
            update_infeasible_cache_using_arith(x);
        }

        void undo_set_updt(var x, interval_set * old_set) {
            if (x < m_infeasible.size()) {
                if(m_infeasible[x] != nullptr){
                    m_ism.dec_ref(m_infeasible[x]);
                }
                m_infeasible[x] = old_set;
                m_infeasible_var_trail.pop_back();
                m_infeasible_prop--;
            }
        }

        void undo_new_stage() {
            SASSERT(m_scope_stage >= 1);
            m_scope_stage--;
        }

        void undo_new_level(bool_var b, var v) {
            SASSERT(m_scope_lvl > 0);
            m_scope_lvl--;
            m_evaluator.pop(1);
            if(m_atoms[b] != nullptr) {
                SASSERT(v != null_var);
                m_var_max_level[v]--;
            }
        }

        void undo_updt_eq(var v, atom * a) {
            if (m_var2eq.size() > v)
                m_var2eq[v] = a; 
        }

        void undo_semantics_decision(var v) {
            // do nothing
        }

        /**
          \brief For bool variables:
          1. branch means deciding bool variables, not for propagated bool vars
          2. both decisions and propogates have bvar assignment
          3. a bool var must be assigned soon after it is branched
          4. the difference is when to insert heap and record stage number
             4.1 decision vars: branch and undo branch
             4.2 assigned vars: assignment
        */
        void undo_branch(hybrid_var old_v) {
            m_hybrid_find_stage[m_hk] = null_var;
            if(hybrid_is_bool(m_hk)) {
                SASSERT(m_decision_bools.contains(m_hk));
                m_decision_bools.erase(m_hk);
            }
            m_var_heap.insert(m_hk);
            m_hk = old_v;
        }

        void undo_bvar_assignment(bool_var b) {
            m_bvalues[b] = l_undef;
            m_levels[b]  = UINT_MAX;
            m_arith_level[b] = default_arith_level;
            del_jst(m_allocator, m_justifications[b]);
            m_justifications[b] = null_justification;
            m_valued_atom_table.erase(b);
            m_assigned_atom_indices[b] = null_var;
            m_valued_atom_trail.pop_back();
            m_atom_prop--;
            if(m_atoms[b] == nullptr){ // fresh bool var
                bool_var pure_b = m_pure_bool_convert[b];
                update_unit_after_var_unassigned(pure_b);
                update_infeasible_cache_using_bool(pure_b);
                m_hybrid_assigned_indices[pure_b] = null_var;
                if(!m_decision_bools.contains(pure_b)) { // propagated bool var
                    m_var_heap.insert(b);
                    m_hybrid_find_stage[pure_b] = null_var;
                }
                m_hybrid_trail.pop_back();
                m_bool_trail.pop_back();
                m_hybrid_var_clause_prop--;
                m_hybrid_var_learned_prop--;
            }
        }

        template<typename Predicate>
        void undo_until(Predicate const & pred) {
            while (pred() && !m_trail.empty()) {
                trail & t = m_trail.back();
                // we pop back before undo, because undo may inserting new trails
                // for example, undo avar assignment may insert new bvar assignment trails for new unit atoms
                m_trail.pop_back();
                switch (t.m_kind) {
                    case trail::BVAR_ASSIGNMENT:
                        undo_bvar_assignment(t.m_x);
                        break;
                    case trail::INFEASIBLE_UPDT:
                        undo_set_updt(t.m_x, t.m_old_set);
                        break;
                    case trail::NEW_STAGE:
                        undo_new_stage();
                        break;
                    case trail::NEW_LEVEL:
                        undo_new_level(t.m_x, t.m_x2);
                        break;
                    case trail::UPDT_EQ:
                        undo_updt_eq(t.m_x, t.m_old_eq);
                        break;
                    case trail::ARITH_ASSIGNMENT:
                        undo_avar_assignment(t.m_x);
                        break;
                    case trail::SEMANTICS_DECISION:
                        undo_semantics_decision(t.m_x);
                        break;
                    case trail::BRANCH:
                        undo_branch(t.m_x);
                        break;

                    default:
                        UNREACHABLE();
                }
            }
        }
        
        struct size_pred {
            svector<trail> & m_trail;
            unsigned         m_old_size;
            size_pred(svector<trail> & trail, unsigned old_size):m_trail(trail), m_old_size(old_size) {}
            bool operator()() const { return m_trail.size() > m_old_size; }
        };
        
        // Keep undoing until trail has the given size
        void undo_until_size(unsigned old_size) {
            SASSERT(m_trail.size() >= old_size);
            undo_until(size_pred(m_trail, old_size));
        }

        struct stage_pred {
            var const & m_xk;
            var         m_target;
            stage_pred(var const & xk, var target):m_xk(xk), m_target(target) {}
            bool operator()() const { return m_xk != m_target; }
        };

        // Keep undoing until stage is new_xk
        void undo_until_stage(unsigned new_stage) {
            if(new_stage == null_var){
                new_stage = 0;
            }
            undo_until(stage_pred(m_scope_stage, new_stage));
        }

        struct level_pred {
            unsigned const & m_scope_lvl;
            unsigned         m_new_lvl;
            level_pred(unsigned const & scope_lvl, unsigned new_lvl):m_scope_lvl(scope_lvl), m_new_lvl(new_lvl) {}
            bool operator()() const { return m_scope_lvl > m_new_lvl; }
        };

        // Keep undoing until level is new_lvl
        void undo_until_level(unsigned new_lvl) {
            DTRACE(std::cout << "undo until level " << new_lvl << " ..." << std::endl;);
            undo_until(level_pred(m_scope_lvl, new_lvl));
        }

        struct unassigned_pred {
            bool_var               m_b;
            svector<lbool> const & m_bvalues;
            unassigned_pred(svector<lbool> const & bvalues, bool_var b):
                m_b(b),
                m_bvalues(bvalues) {}
            bool operator()() const { return m_bvalues[m_b] != l_undef; }
        };

        struct arith_unassigned_pred {
            var m_x;
            const assignment & m_assignment;
            arith_unassigned_pred(assignment const & ass, var x): m_assignment(ass), m_x(x) {}
            bool operator()() const {
                return m_assignment.is_assigned(m_x);
            }
        };

        void undo_until_unassigned(hybrid_var x, bool is_bool){
            if(is_bool){
                DTRACE(std::cout << "undo until pure bool " << x << " unassigned..." << std::endl;);
                undo_until(unassigned_pred(m_bvalues, m_pure_bool_vars[x]));
                SASSERT(m_bvalues[b] == l_undef);
            }
            else {
                DTRACE(std::cout << "undo until arith " << x << " unassigned..." << std::endl;);
                undo_until(arith_unassigned_pred(m_assignment, x));
                SASSERT(!m_assignment.is_assigned(x));
            }
        }

        struct true_pred {
            bool operator()() const { return true; }
        };

        void undo_until_empty() {
            undo_until(true_pred());
        }

        /**
           \brief Create a new scope level
        */
        void new_level(bool_var b) {
            m_evaluator.push();
            m_scope_lvl++;
            if(m_atoms[b] != nullptr) {
                var v = find_unassigned_var(b);
                m_var_max_level[v]++;
                save_new_level_trail(b, v);
            } else {
                save_new_level_trail(b, null_var);
            }
        }

        var find_unassigned_var(bool_var b) const {
            var res = null_var;
            unsigned num_undef = 0;
            for(var v: m_nlsat_atoms[b]->m_vars) {
                if(!m_assignment.is_assigned(v)) {
                    num_undef ++;
                    res = v;
                    if(num_undef > 1) {
                        UNREACHABLE();
                    }   
                }
            }
            SASSERT(num_undef == 1);
            return res;
        }

        /**
           \brief Return the value of the given literal that was assigned by the search
           engine.
        */
        lbool assigned_value(literal l) const {
            bool_var b = l.var();
            if (l.sign())
                return ~m_bvalues[b];
            else
                return m_bvalues[b];
        }

        arith_level get_arith_level(bool_var b) const {
            if(m_atoms[b] == nullptr) {
                return default_arith_level;
            }
            var v = find_unassigned_var(b);
            return arith_level(v, m_var_max_level[v]);
        }

        /**
           \brief Assign literal using the given justification
         */
        void assign_literal(literal l, justification j) {
            if(m_valued_atom_table.contains(l.var())) { // assigned previously
                return;
            }
            DTRACE(std::cout << "assign literal: "; display(std::cout, l) << std::endl;);
            SASSERT(assigned_value(l) == l_undef);
            SASSERT(j != null_justification);
            SASSERT(!j.is_null());
            if (j.is_decision()) {
                DTRACE(std::cout << "[decision] " << m_scope_lvl << std::endl;);
                m_decisions++;
            } else if(j.is_clause()) {
                DTRACE(std::cout << "[unit propagate]" << std::endl;);
                m_unit_propagate++;
                if(l.var() == 91 || l.var() == 101) {
                    display(std::cout, *j.get_clause()) << std::endl;;
                }
            } else if(j.is_lazy()) {
                DTRACE(std::cout << "[lazy propagate]" << std::endl;);
                m_real_propagate++;
            }
            bool_var b   = l.var();
            m_bvalues[b] = to_lbool(!l.sign());
            m_levels[b]  = m_scope_lvl;
            m_arith_level[b] = get_arith_level(b);
            m_justifications[b] = j;
            save_bool_assign_trail(b);
            updt_eq(b, j);
            m_assigned_atom_indices[l.var()] = m_valued_atom_trail.size();
            m_valued_atom_trail.push_back(l.var());
            m_valued_atom_table.insert(l.var());
            if(m_atoms[b] == nullptr) { // in case the assigned literal is boolean
                bool_var pure_b = m_pure_bool_convert[b];
                m_bool_trail.push_back(pure_b);
                m_hybrid_trail.push_back(pure_b);
                m_hybrid_assigned_indices[pure_b] = m_hybrid_trail.size() - 1;
                if(!m_decision_bools.contains(pure_b)) {
                    m_hybrid_find_stage[pure_b] = m_scope_stage;
                }
                check_clause_status_using_hybrid_var();
                check_learned_status_using_hybrid_var();
            }
            DTRACE(std::cout << "assign literal done" << std::endl;);
        }

        void decide_literal(literal l) {
            new_level(l.var());
            assign_literal(l, decided_justification);
        }

        lbool value(literal l){
            lbool val = assigned_value(l);
            if(val != l_undef){
                return val;
            }
            bool_var b = l.var();
            if(m_atoms[b] == nullptr){
                return l_undef;
            }
            if(!all_assigned(m_atoms[b])){
                return l_undef;
            }
            return to_lbool(m_evaluator.eval(m_atoms[b], l.sign()));
        }

        bool all_assigned(atom const *a) const {
            if(a == nullptr) {
                return true;
            }
            for(var v: m_nlsat_atoms[a->bvar()]->m_vars) {
                if(!m_assignment.is_assigned(v)) {
                    return false;
                }
            }
            return true;
        }
        
        /**
           \brief assign l to true, because l + (justification of) s is infeasible in RCF in the current interpretation.
        */
        literal_vector core;
        ptr_vector<clause> clauses;
        void R_propagate(literal l, interval_set const * s, bool include_l = true) {
            m_ism.get_justifications(s, core, clauses);
            if (include_l) 
                core.push_back(~l);
            assign_literal(l, mk_lazy_jst(m_allocator, core.size(), core.data(), clauses.size(), clauses.data()));
            SASSERT(value(l) == l_true);
        }

        /**
           \brief Update m_var2eq mapping.
        */
        void updt_eq(bool_var b, justification j) {
            if (!m_simplify_cores)
                return;
            if (m_bvalues[b] != l_true)
                return;
            atom * a = m_atoms[b];
            if (a == nullptr || a->get_kind() != atom::EQ || to_ineq_atom(a)->size() > 1 || to_ineq_atom(a)->is_even(0))
                return;
            switch (j.get_kind()) {
                case justification::CLAUSE:
                    if (j.get_clause()->assumptions() != nullptr) return;
                    break;            
                case justification::LAZY:
                    if (j.get_lazy()->num_clauses() > 0) return;
                    if (j.get_lazy()->num_lits() > 0) return;
                    break;
                default:
                    break;
            }
            // Static order: save equality for max var
            // Dynamic order: 
            // 1. for ineq atom: save each var
            // 2. for root atom: save root var
            if(a->is_ineq_atom()) {
                for(var v: m_nlsat_atoms[b]->m_vars) {
                    if(m_var2eq[v] != nullptr && degree_atom(m_var2eq[v], v) < degree_atom(a, v)) {
                        continue;
                    }
                    save_updt_eq_trail(v, m_var2eq[v]);
                    m_var2eq[v] = a;
                }
            } else if(a->is_root_atom()) {
                var v = to_root_atom(a)->x();
                if(m_var2eq[v] != nullptr && degree_atom(m_var2eq[v], v) < degree_atom(a, v)) {
                    return;
                }
                save_updt_eq_trail(v, m_var2eq[v]);
                m_var2eq[v] = a;
            } else {
                UNREACHABLE();
            }
        }

        unsigned degree_atom(atom const * a, var x) const {
            if(a == nullptr) return 0;
            if(a->is_root_atom()) return m_pm.degree(to_root_atom(a)->p(), x);
            SASSERT(a->is_ineq_atom());
            ineq_atom const *aa = to_ineq_atom(a);
            unsigned res = 0;
            for(unsigned i = 0; i < aa->size(); i++) {
                res += m_pm.degree(aa->p(i), x);
            }
            return res;
        }

        void check_overall_satisfied() {
            for(unsigned i = 0; i < m_clauses.size(); i++){
                if(!is_clause_sat(m_clauses[i])){
                    UNREACHABLE();
                }
            }
        }

        bool is_clause_sat(clause const * cls) {
            for(literal l: *cls){
                if(is_literal_sat(l)){
                    return true;
                }
            }
            return false;
        }

        inline bool lbool2bool(lbool r) const {
            SASSERT(r != l_undef);
            return r == l_true;
        }

        bool is_literal_sat(literal l) {
            return is_bool_literal(l) ? (m_bvalues[l.var()] != l_undef && lbool2bool(m_bvalues[l.var()]) != l.sign())
                                      : (all_assigned(m_atoms[l.var()]) && m_evaluator.eval(m_atoms[l.var()], l.sign()));
        }

        void restart(){
            init_search();
        }

        bool process_hybrid_clause(clause const & cls){
            unsigned first_undef = UINT_MAX, num_undef = 0;
            interval_set_ref first_undef_set(m_ism);
            interval_set_ref curr_st(m_ism);
            for(unsigned idx = 0; idx < cls.size(); idx++) {
                literal l = cls[idx];
                checkpoint();
                lbool val = value(l);
                if(val == l_true) 
                    return true;
                if(val == l_false) 
                    continue;
                SASSERT(val == l_undef);
                bool_var b = l.var();
                atom *a = m_atoms[b];
                if(a != nullptr) { // arith literal
                    var v = hybrid2arith(m_hk);
                    curr_st = m_evaluator.infeasible_intervals(a, l.sign(), &cls, v);
                    // empty infeasible --> true
                    if(m_ism.is_empty(curr_st)){
                        R_propagate(l, nullptr);
                        return true;
                    }
                    // full infeasible --> false
                    if(m_ism.is_full(curr_st)){
                        R_propagate(~l, nullptr);
                        continue;
                    }
                    // subset --> true
                    if(m_ism.subset(curr_st, m_infeasible[v])){
                        R_propagate(l, m_infeasible[v]);
                        return true;
                    }
                    // complement --> false
                    interval_set_ref tmp(m_ism);
                    tmp = m_ism.mk_union(curr_st, m_infeasible[v]);
                    if(m_ism.is_full(tmp)){
                        R_propagate(~l, tmp, false);
                        continue;
                    }
                }
                num_undef++;
                if(first_undef == UINT_MAX){
                    first_undef = idx;
                    first_undef_set = curr_st;
                }
            }
            if(num_undef == 0) {
                return false;
            } else if(num_undef == 1) { // unit propagate
                assign_literal(cls[first_undef], mk_clause_jst(&cls));
                if(m_atoms[cls[first_undef].var()] != nullptr) {
                    var v = hybrid2arith(m_hk);
                    update_infeasible_set(v, first_undef_set);
                }
            } else {
                decide_literal(cls[first_undef]);
                if(m_atoms[cls[first_undef].var()] != nullptr) {
                    var v = hybrid2arith(m_hk);
                    update_infeasible_set(v, first_undef_set);
                }
            }
            return true;
        }

        /**
           \brief using arith variable assignment trail to propagate valued literals
           \example x + y >= 12 is watched by arith var x and y
           When one of the vars is assigned, loop all its watches, find replacement (unassigned)

           \if unit watch or another watcher is assigned, the literal is valued (push intto valued trail)
           \elseif found another watcher, replace and unwatch
           \else unit to another watcher, still watch
        */
        void check_atom_status_using_arith() {
            DTRACE(std::cout << "use arith assignment to check atom" << std::endl;);
            while(m_arith_atom_prop < m_arith_trail.size()) {
                var curr_var = m_arith_trail[m_arith_atom_prop++];
                std::cout << "curr var: " << curr_var << std::endl;
                vector<atom_var_watcher*> &watches = m_var_watching_atoms[curr_var];
                int i, j = 0, size = watches.size();
                for(i = 0; i < size; i++) {
                    var another_var = watches[i]->get_another_var(curr_var);
                    SASSERT(another_var != null_var); // unit atom shall not be watched
                    int idx = watches[i]->m_atom_index;
                    if (m_assignment.is_assigned(another_var)) { // totally assigned
                        if(!m_valued_atom_table.contains(idx)) { // the atom may be assigned previously by unit propagation
                            m_assigned_atom_indices[idx] = m_valued_atom_trail.size();
                            m_valued_atom_trail.push_back(idx);
                            m_valued_atom_table.insert(idx);
                        }
                        watches[j++] = watches[i];
                    } else { // try to find another watched var
                        var new_watched_var = null_var;
                        for (var v : m_nlsat_atoms[idx]->m_vars) {
                            if (!m_assignment.is_assigned(v) && v != curr_var && v != another_var) {
                                new_watched_var = v;
                                break;
                            }
                        }
                        if(new_watched_var != null_var) { // change watches
                            watches[i]->replace_var(curr_var, new_watched_var);
                            m_var_watching_atoms[new_watched_var].push_back(watches[i]);
                        } else { // still watch, unit literal to another var
                            watches[j++] = watches[i];
                            if(m_atoms[idx]->is_ineq_atom() || to_root_atom(m_atoms[idx])->x() == another_var) {
                                insert_unit_atom(idx, another_var);
                            }
                        }
                    }
                }
                watches.shrink(j);
            }
            DTRACE(std::cout << "check atom done" << std::endl;);
        }

        bool is_hybrid_assigned(hybrid_var x) const {
            if(x == null_var) {
                return false;
            }
            return x < num_bool_vars() ? m_bvalues[m_pure_bool_vars[x]] != l_undef : m_assignment.is_assigned(x - num_bool_vars());
        }

        /**
           \brief using hybrid variable to check clause real-unit status
           \example x + y >= 12 \/ x y <= -8 \/ b
           When x and y are assigned, clause is unit to b (also unit propagation)
           When x and b are assigned, clause is unit to x (real-unit)

           \if another var is also assigned, the clause is conflict
           \elseif find replacement, replace and change watch
           \else unit to another var, update infeasible information
        */
        clause* real_propagate_clauses() {
            DTRACE(std::cout << "rp clauses" << std::endl;);
            unsigned sz = 0;
            for(var v = 0; v < num_arith_vars(); v++) {
                for(unsigned idx: m_newly_unit_arith_clauses[v]) {
                    sz++;
                    if (!update_clause_infeasible_set(idx, v)) { // conflict
                        direct_stage_to_conflict_var(arith2hybrid(v));
                        return m_arith_unit_clauses_more_lits[v].empty() ? m_clauses[idx] : process_and_decide_literals_while_conflict();
                    } else {
                        if (m_clauses[idx]->is_unit()) {
                            assign_literal((*m_clauses[idx])[0], mk_clause_jst(m_clauses[idx]));
                        }
                    }
                }
            }
            m_newly_unit_arith_clauses.clear();
            m_newly_unit_arith_clauses.resize(num_arith_vars(), var_vector(0));
            return nullptr;
        }

        /**
           \brief using hybrid variable to check learned real-unit status
        */
        clause* real_propagate_learned() {
            DTRACE(std::cout << "rp learned" << std::endl;);
            unsigned sz = 0;
            for(var v = 0; v < num_arith_vars(); v++) {
                for(unsigned idx: m_newly_unit_arith_learned[v]) {
                    sz++;
                    if(!update_learned_infeasible_set(idx, v)) { // conflict
                        std::cout << "idx: " << idx << std::endl;
                        display(std::cout, *m_learned[idx]);
                        direct_stage_to_conflict_var(arith2hybrid(v));
                        return m_arith_unit_learned_more_lits[v].empty() ? m_learned[idx] : process_and_decide_literals_while_conflict();
                    } else {
                        if(m_learned[idx]->is_unit()) {
                            assign_literal((*m_learned[idx])[0], mk_clause_jst(m_learned[idx]));
                        }
                    }
                }
            }
            m_newly_unit_arith_learned.clear();
            m_newly_unit_arith_learned.resize(num_arith_vars(), var_vector(0));
            return nullptr;
        }

        /**
          \brief When we face a conflict of an arith var, we direct the stage to that var
        */
        void direct_stage_to_conflict_var(hybrid_var v) {
            DTRACE(std::cout << "direct stage to conflict var: " << v << std::endl;);
            if(v == null_var) {
                return;
            }
            new_stage();
            save_branch_trail(m_hk, v);
            m_hk = v;
            m_hybrid_find_stage[m_hk] = m_scope_stage;
        }

        /**
          \brief When we face a conflict of a clause, we direct the stage until the clause is unit unassigned
          \example x >= 23, y <= 18, x < 0 \/ y > 40
                    clause 3 is conflict, and we should update stage until the clause is unit unassigned
          \note In this special situation, the unassigned vars can only be arith
          \proof Suppose we have a conflict clause with unassigned bool var, 
          then it must a literal unassigned,  then it has uncertained value
        */
        void direct_stage_to_conflict_clause(unsigned idx) {
            DTRACE(std::cout << "direct stage to conflict clause: " << idx << std::endl;
                display(std::cout, *m_clauses[idx]) << std::endl;
            );
            var_vector vec;
            get_unassigned_clause_arith_vars(idx, vec);
            if(vec.empty()) {
                return;
            }
            for(unsigned i = 0; i < vec.size() - 1; i++) {
                hybrid_var v = arith2hybrid(vec[i]);
                new_stage();
                save_branch_trail(m_hk, v);
                m_hk = v;
                m_hybrid_find_stage[m_hk] = m_scope_stage;
                choose_value();
            }
            hybrid_var v = arith2hybrid(vec.back());
            new_stage();
            save_branch_trail(m_hk, v);
            m_hk = v;
            m_hybrid_find_stage[m_hk] = m_scope_stage;
        }

        void direct_stage_to_conflict_learned(unsigned idx) {
            DTRACE(std::cout << "direct stage to conflict learned: " << idx << std::endl;
                display(std::cout, *m_learned[idx]) << std::endl;
            );
            var_vector vec;
            get_unassigned_learned_arith_vars(idx, vec);
            if(vec.empty()) {
                return;
            }
            for(unsigned i = 0; i < vec.size() - 1; i++) {
                hybrid_var v = arith2hybrid(vec[i]);
                new_stage();
                save_branch_trail(m_hk, v);
                m_hk = v;
                m_hybrid_find_stage[m_hk] = m_scope_stage;
                choose_value();
            }
            hybrid_var v = arith2hybrid(vec.back());
            new_stage();
            save_branch_trail(m_hk, v);
            m_hk = v;
            m_hybrid_find_stage[m_hk] = m_scope_stage;
        }

        void get_unassigned_clause_arith_vars(unsigned idx, var_vector & vec) {
            vec.clear();
            for(var v: m_nlsat_clauses[idx]->m_vars) {
                if(!m_assignment.is_assigned(v)) {
                    vec.push_back(v);
                }
            }
        }

        void get_unassigned_learned_arith_vars(unsigned idx, var_vector & vec) {
            vec.clear();
            for(var v: m_nlsat_learned[idx]->m_arith_vars) {
                if(!m_assignment.is_assigned(v)) {
                    vec.push_back(v);
                }
            }
        }

        /**
          \brief When we face a conflict, use semantics decision for clauses with more literals
          \note If all clauses are unit, no need for semantics decision and won't enter this function
        */
        clause* process_and_decide_literals_while_conflict() {
            DTRACE(std::cout << "clause level conflict, semantics decision" << std::endl;);
            var v = hybrid2arith(m_hk);
            DTRACE(std::cout << "v: " << v << std::endl; m_display_var(std::cout, v) << std::endl;);
            DTRACE(display_clause_vector(std::cout, m_arith_unit_clauses[v]););
            DTRACE(display_clause_vector(std::cout, m_arith_unit_learned[v]););
            DTRACE(display_assignment(std::cout););
            SASSERT(m_arith_unit_clauses_more_lits[v].size() + m_arith_unit_learned_more_lits.size() > 0);
            save_semantics_decision_trail(v);
            save_set_updt_trail(v, m_infeasible[v]);
            m_infeasible[v] = nullptr;
            for(int idx: m_arith_unit_clauses[v]) {
                if(!process_hybrid_clause(*m_clauses[idx])) {
                    return m_clauses[idx];
                }
            }
            for(int idx: m_arith_unit_learned[v]) {
                if(!process_hybrid_clause(*m_learned[idx])) {
                    return m_learned[idx];
                }
            }
            UNREACHABLE();
            return nullptr;
        }

        /**
          \brief Under what situation does the arith var is unit to the learned clause
          \param m_rp_vars: poly vars except root one in root atoms
        */
        bool check_learned_unit(int idx, var x) const {
            return !m_nlsat_learned[idx]->m_rp_vars.contains(x);
        }

        void update_infeasible_set(var v, interval_set const *s) {
            DTRACE(std::cout << "interval set s: "; m_ism.display(std::cout, s) << std::endl;);
            interval_set_ref union_st(m_ism);
            union_st = m_ism.mk_union(s, m_infeasible[v]);
            SASSERT(!m_ism.is_full(union_st));
            save_set_updt_trail(v, m_infeasible[v]);
            if(union_st != nullptr) {
                m_ism.inc_ref(union_st);
            }
            m_infeasible[v] = union_st;
        }

        /**
          \brief Update arith var's front end infeasible set using original clause idx
        */
        bool update_clause_frontend_infeasible_set(int idx, var arith_var) {
            interval_set_ref curr_st(m_ism);
            curr_st = get_clause_infeasible_set(idx, arith_var);
            interval_set_ref union_st(m_ism);
            union_st = m_ism.mk_union(curr_st, m_frontend_infeasible[arith_var]);
            if(m_ism.is_full(union_st)) { // conflict
                return false;
            } else { // consistent, just update infeasible set
                if(union_st != nullptr) {
                    m_ism.inc_ref(union_st);
                }
                m_frontend_infeasible[arith_var] = union_st;
                return true;
            }
        }

        /**
          \brief Update arith var's front end infeasible set using learned clause idx
        */
        bool update_learned_frontend_infeasible_set(int idx, var arith_var) {
            interval_set_ref curr_st(m_ism);
            curr_st = get_learned_infeasible_set(idx, arith_var);
            interval_set_ref union_st(m_ism);
            union_st = m_ism.mk_union(curr_st, m_frontend_infeasible[arith_var]);
            if(m_ism.is_full(union_st)) { // conflict
                return false;
            } else { // consistent, just update infeasible set
                if(union_st != nullptr) {
                    m_ism.inc_ref(union_st);
                }
                m_frontend_infeasible[arith_var] = union_st;
                return true;
            }
        }

        /**
          \return Whether updating clause infeasible set causes conflict
        */
        bool update_clause_infeasible_set(int idx, var arith_var) {
            interval_set_ref curr_st(m_ism);
            curr_st = get_clause_infeasible_set(idx, arith_var);
            interval_set_ref union_st(m_ism);
            union_st = m_ism.mk_union(curr_st, m_infeasible[arith_var]);
            if(m_ism.is_full(union_st)) { // conflict
                return false;
            } else { // consistent, just update infeasible set
                save_set_updt_trail(arith_var, m_infeasible[arith_var]);
                if(union_st != nullptr) {
                    m_ism.inc_ref(union_st);
                }
                m_infeasible[arith_var] = union_st;
                propagate_literal_using_infeasible();
                return true;
            }
        }

        /**
          \return Whether updating clause infeasible set causes conflict
        */
        bool update_learned_infeasible_set(int idx, var arith_var) {
            interval_set_ref curr_st(m_ism);
            curr_st = get_learned_infeasible_set(idx, arith_var);
            interval_set_ref union_st(m_ism);
            union_st = m_ism.mk_union(curr_st, m_infeasible[arith_var]);
            if(m_ism.is_full(union_st)) { // conflict
                return false;
            } else { // consistent, just update infeasible set
                save_set_updt_trail(arith_var, m_infeasible[arith_var]);
                if(union_st != nullptr) {
                    m_ism.inc_ref(union_st);
                }
                m_infeasible[arith_var] = union_st;
                propagate_literal_using_infeasible();
                return true;
            }
        }

        /**
          \brief Given an atom index, return its bool value
        */
        lbool value_atom(bool_var b) {
            if(m_bvalues[b] != l_undef) {
                return m_bvalues[b];
            }
            if(m_atoms[b] == nullptr) {
                return l_undef;
            }
            if(!arith_atom_assigned(b)) {
                return l_undef;
            }
            return to_lbool(m_evaluator.eval(m_atoms[b], false));
        }

        clause* propagate_unit_clause_using_atom(unsigned idx) {
            DTRACE(std::cout << "propagate unit clauses" << std::endl;);
            if(m_atom_unit_clauses[idx] != null_var) {
                clause const &cls = *m_clauses[m_atom_unit_clauses[idx]];
                literal l = cls[0];
                if(value(l) == l_false) {
                    direct_stage_to_conflict_clause(m_atom_unit_clauses[idx]);
                    return m_clauses[m_atom_unit_clauses[idx]];
                }
            }
            return nullptr;
        }

        clause* propagate_unit_learned_using_atom(unsigned idx) {
            DTRACE(std::cout << "propagate unit learned" << std::endl;);
            if(m_atom_unit_learned[idx] != null_var) {
                clause const &cls = *m_learned[m_atom_unit_learned[idx]];
                literal l = cls[0];
                if(value(l) == l_false) {
                    direct_stage_to_conflict_learned(m_atom_unit_learned[idx]);
                    return m_learned[m_atom_unit_learned[idx]];
                }
            }
            return nullptr;
        }

        clause* propagate_clause_using_atom_watcher(unsigned idx) {
            DTRACE(std::cout << "propagate more clauses" << std::endl;);
            vector<clause_literal_watcher *> &watches = value_atom(idx) == l_true ? // assign positive, scan negative; assign negative, scan positive
                            m_neg_literal_watching_clauses[idx] : m_pos_literal_watching_clauses[idx];
            int i, j = 0, size = watches.size();
            for(i = 0; i < size; i++) {
                int c_idx = watches[i]->m_clause_index;
                int l1 = watches[i]->l1, l2 = watches[i]->l2;
                // the watches have already been changed (this may happen after the loop of first watcher)
                // this case only happens for SMT, 
                // since in "multi-valued" problem, two watches can be assigned and changed simutaneously
                if(abs(l1) != idx && abs(l2) != idx) { // watches have been updated, adopt it
                    continue;
                }
                lbool v1 = get_literal_value(l1), v2 = get_literal_value(l2);
                SASSERT(v1 == l_false || v2 == l_false); // must have a false literal, since we assign one of the literals
                if(v1 == l_true || v2 == l_true) { // the clause is already satisfied, keep watch and loop next
                    watches[j++] = watches[i];
                    continue;
                } else if(v1 == l_false && v2 == l_false) { // both are false, this is caused by arith assignment
                    int new_l1 = 0, new_l2 = 0;
                    int unit_index = -1;
                    clause const &cls = *m_clauses[c_idx]; 
                    bool sat = false;
                    for (int looped_idx = 0; looped_idx < cls.size(); looped_idx++) {
                        literal l = cls[looped_idx];
                        if(l.var() == v1 || l.var() == v2 || value(l) == l_false) {
                            continue;
                        }
                        if(value(l) == l_true) {
                            sat = true;
                            break;
                        }
                        if(new_l1 == 0) {
                            unit_index = looped_idx;
                            new_l1 = l.sign() ? -l.var() : l.var();
                        } else if(new_l2 == 0) {
                            new_l2 = l.sign() ? -l.var() : l.var();
                        } else {
                            break;
                        }
                    }
                    if(sat) { // sat clause
                        watches[j++] = watches[i];
                        continue;
                    }
                    if(new_l1 != 0 && new_l2 != 0) { // change both watches
                        watches[i]->replace_literal(l1, new_l1);
                        watches[i]->replace_literal(l2, new_l2);
                        if(new_l1 > 0) {
                            m_pos_literal_watching_clauses[new_l1].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_clauses[-new_l1].push_back(watches[i]);
                        }
                        if(new_l2 > 0) {
                            m_pos_literal_watching_clauses[new_l2].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_clauses[-new_l2].push_back(watches[i]);
                        }
                    } else if(new_l1 == 0 && new_l2 == 0) { // conflict clause
                        watches[j++] = watches[i];
                        direct_stage_to_conflict_clause(c_idx);
                        return m_clauses[c_idx];
                    } else { // change one of them, then propagate
                        SASSERT(new_l1 != 0 && new_l2 == 0);
                        watches[i]->replace_literal_using_abs(idx, new_l1);
                        if(new_l1 > 0) {
                            m_pos_literal_watching_clauses[new_l1].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_clauses[-new_l1].push_back(watches[i]);
                        }
                        if(is_bool_literal(cls[unit_index])) {
                            assign_literal(cls[unit_index], mk_clause_jst(&cls));
                        }
                    }
                } else { // current literal is false, the other is undef
                    int new_l = 0, another_idx = watches[i]->get_another_literal_index_using_abs(idx);
                    clause const &cls = *m_clauses[c_idx];
                    bool sat = false;
                    for(int looped_idx = 0; looped_idx < cls.size(); looped_idx++) {
                        literal l = cls[looped_idx];
                        if(l.var() == abs(another_idx)) {
                            another_idx = looped_idx;
                            continue;
                        }
                        if(l.var() == idx || value(l) == l_false) {
                            continue;
                        }
                        if(value(l) == l_true) {
                            sat = true;
                            break;
                        }
                        new_l = l.sign() ? -l.var() : l.var();
                        break;
                    }
                    if(sat) {
                        watches[j++] = watches[i];
                        continue;
                    }
                    if(new_l != 0) { // found replacement
                        watches[i]->replace_literal_using_abs(idx, new_l);
                        if(new_l > 0) {
                            m_pos_literal_watching_clauses[new_l].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_clauses[-new_l].push_back(watches[i]);
                        }
                    } else { // unit to another literal, still watch
                        if(is_bool_literal(cls[another_idx])) {
                            assign_literal(cls[another_idx], mk_clause_jst(&cls));
                        }
                        watches[j++] = watches[i];
                    }
                }
                if(c_idx == 128) {
                    std::cout << "l1: " << watches[i]->l1 << " l2: " << watches[i]->l2 << std::endl;
                    std::cout << "current atom: " << idx << std::endl;
                    for(auto ele: m_neg_literal_watching_clauses[63]) {
                        if(ele->m_clause_index == 128) {
                            std::cout << "contains" << std::endl;
                            break;
                        }
                    }
                }
            }
            watches.shrink(j);
            return nullptr;
        }

        clause* propagate_learned_using_atom_watcher(unsigned idx) {
            DTRACE(std::cout << "propagate more learned" << std::endl;);
            vector<clause_literal_watcher *> &watches = value_atom(idx) == l_true ? // assign positive, scan negative; assign negative, scan positive
                        m_neg_literal_watching_learned[idx] : m_pos_literal_watching_learned[idx];
            int j = 0, size = watches.size();
            for(int i = 0; i < size; i++) {
                int c_idx = watches[i]->m_clause_index;
                int l1 = watches[i]->l1, l2 = watches[i]->l2;
                // the watches have already been changed (this may happen after the loop of first watcher)
                // this case only happens for SMT, 
                // since in "multi-valued" problem, two watches can be assigned and changed simutaneously
                if(abs(l1) != idx && abs(l2) != idx) { // watches have been updated, adopt it
                    continue;
                }
                lbool v1 = get_literal_value(l1), v2 = get_literal_value(l2);
                SASSERT(v1 == l_false || v2 == l_false); // must have a false literal, since we assign one of the literals
                if(v1 == l_true || v2 == l_true) { // the clause is already satisfied, keep watch and loop next
                    watches[j++] = watches[i];
                    continue;
                } else if(v1 == l_false && v2 == l_false) { // both are false, this is caused by arith assignment
                    int new_l1 = 0, new_l2 = 0;
                    int unit_index = -1;
                    clause const &cls = *m_learned[c_idx]; 
                    bool sat = false;
                    for (int looped_idx = 0; looped_idx < cls.size(); looped_idx++) {
                        literal l = cls[looped_idx];
                        if(l.var() == v1 || l.var() == v2 || value(l) == l_false) {
                            continue;
                        }
                        if(value(l) == l_true) {
                            sat = true;
                            break;
                        }
                        if(new_l1 == 0) {
                            unit_index = looped_idx;
                            new_l1 = l.sign() ? -l.var() : l.var();
                        } else if(new_l2 == 0) {
                            new_l2 = l.sign() ? -l.var() : l.var();
                        } else {
                            break;
                        }
                    }
                    if(sat) { // sat clause
                        watches[j++] = watches[i];
                        continue;
                    }
                    if(new_l1 != 0 && new_l2 != 0) { // change both watches
                        watches[i]->replace_literal(l1, new_l1);
                        watches[i]->replace_literal(l2, new_l2);
                        if(new_l1 > 0) {
                            m_pos_literal_watching_learned[new_l1].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_learned[-new_l1].push_back(watches[i]);
                        }
                        if(new_l2 > 0) {
                            m_pos_literal_watching_learned[new_l2].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_learned[-new_l2].push_back(watches[i]);
                        }
                    } else if(new_l1 == 0 && new_l2 == 0) { // conflict clause
                        watches[j++] = watches[i];
                        direct_stage_to_conflict_learned(c_idx);
                        return m_learned[c_idx];
                    } else { // change one of them, then propagate
                        SASSERT(new_l1 != 0 && new_l2 == 0);
                        watches[i]->replace_literal_using_abs(idx, new_l1);
                        if(new_l1 > 0) {
                            m_pos_literal_watching_learned[new_l1].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_learned[-new_l1].push_back(watches[i]);
                        }
                        if(is_bool_literal(cls[unit_index])) {
                            assign_literal(cls[unit_index], mk_clause_jst(&cls));
                        }
                    }
                } else { // current literal is false, the other is undef
                    int new_l = 0, another_idx = watches[i]->get_another_literal_index_using_abs(idx);
                    clause const &cls = *m_learned[c_idx];
                    bool sat = false;
                    for(int looped_idx = 0; looped_idx < cls.size(); looped_idx++) {
                        literal l = cls[looped_idx];
                        if(l.var() == abs(another_idx)) {
                            another_idx = looped_idx;
                            continue;
                        }
                        if(l.var() == idx || value(l) == l_false) {
                            continue;
                        }
                        if(value(l) == l_true) {
                            sat = true;
                            break;
                        }
                        new_l = l.sign() ? -l.var() : l.var();
                        break;
                    }
                    if(sat) {
                        watches[j++] = watches[i];
                        continue;
                    }
                    if(new_l != 0) { // found replacement
                        watches[i]->replace_literal_using_abs(idx, new_l);
                        if(new_l > 0) {
                            m_pos_literal_watching_learned[new_l].push_back(watches[i]);
                        } else {
                            m_neg_literal_watching_learned[-new_l].push_back(watches[i]);
                        }
                    } else { // unit to another literal, still watch
                        if(is_bool_literal(cls[another_idx])) {
                            assign_literal(cls[another_idx], mk_clause_jst(&cls));
                        }
                        watches[j++] = watches[i];
                    }
                }
            }
            watches.shrink(j);
            return nullptr;
        }

        /**
           \brief Both literals may change after this turn's assigmment, which is different from SAT solver
           \example [x -> 0]  x + y >= 12 \/ x y < -5
                    [x -> 0, y -> 2] both literal become assigned (evaluated to false), and thus generates a conflict
            
            \if When both literals become false, we find replacement for both of them (undef or true)
                \if find nothing: all literals are false, conflict clause
                \elseif find one: replace current literal, change watch
                \else find two: replace both literals, change both of them
            \elseif one literal is false, the other is undef, find replacement for current literal
                \if find nothing: unit propagate
                \else find one: replace current literal, change watch
            \else one literal is false, the other is true.
                  The clause is satisfied, do nothing and keep watching.

            \date 2023/09/11
            \brief we do not assign arith literal in up, since this will cause resolving bugs
                   the only goal of up is to detect conflict clauses and assign boolean literal

            \date 2023/09/14
            \brief Add unit clause in unit propagate, to detect conflict
            \example x + y^2 <= 12, when x -> 100, the atom is propagated to false, while the conflict clause isn't noticed
        */
        clause* unit_propagate() {
            DTRACE(std::cout << "unit propagate" << std::endl;);
            clause* res;
            while(m_atom_prop < m_valued_atom_trail.size()) {
                unsigned idx = m_valued_atom_trail[m_atom_prop++];
                SASSERT(value_atom(idx) != l_undef);
                if((res = propagate_unit_clause_using_atom(idx)) != nullptr) return res;
                if((res = propagate_unit_learned_using_atom(idx)) != nullptr) return res;
                if((res = propagate_clause_using_atom_watcher(idx)) != nullptr) return res;
                if((res = propagate_learned_using_atom_watcher(idx)) != nullptr) return res;
            }
            return nullptr;
        }

        lbool get_literal_value(int idx) {
            lbool res = value_atom(abs(idx));
            return idx >= 0 ? res : ~res;
        }

        bool arith_atom_assigned(bool_var b) const {
            auto const * a = m_nlsat_atoms[b];
            for(var v: a->m_vars){
                if(!m_assignment.is_assigned(v)){
                    return false;
                }
            }
            return true;
        }

        /**
          \brief When infeasible set of an arith var is updated, use this information to determine literal's status
          \note 
          if an atom is also a unit clause, it will be assigned using unit propagation when updating clause's infeasible set
          Actually, real propagating unit clause's literal won't cause any mistake (if consistent),
          but it is a circular argument, 
          i.e. you use the infeasible set computed by the unit clause of the atom to propagate itself
        */
        void propagate_literal_using_infeasible() {
            DTRACE(std::cout << "use infeasible to propagate atom" << std::endl;);
            while(m_infeasible_prop < m_infeasible_var_trail.size()) {
                var v = m_infeasible_var_trail[m_infeasible_prop++];
                for(int idx: m_arith_unit_atom[v]) {
                    if(m_valued_atom_table.contains(idx)) { // Ignore propagated atoms
                        continue;
                    }
                    interval_set_ref curr_st(m_ism);
                    curr_st = get_atom_infeasible_set(idx, v, false);
                    if(m_ism.is_empty(curr_st)) {
                        R_propagate(literal(idx, false), nullptr);
                    } else if(m_ism.is_full(curr_st)) {
                        R_propagate(literal(idx, true), nullptr);
                    } else if(m_ism.subset(curr_st, m_infeasible[v])) {
                        R_propagate(literal(idx, false), m_infeasible[v]);
                    } else {
                        interval_set_ref tmp(m_ism);
                        tmp = m_ism.mk_union(curr_st, m_infeasible[v]);
                        if (m_ism.is_full(tmp)) {
                            R_propagate(literal(idx, true), tmp, false);
                        }
                    }
                }
            }
        }

        bool newly_unit_empty() const {
            for(var v = 0; v < num_arith_vars(); v++) {
                if(!m_newly_unit_arith_clauses[v].empty() || !m_newly_unit_arith_learned[v].empty()) {
                    return false;
                }
            }
            return true;
        }

        bool check_propagate_counter() const {
            return m_atom_prop < m_valued_atom_trail.size() ||
                   m_infeasible_prop < m_infeasible_var_trail.size() ||
                   !newly_unit_empty();
        }

        clause * overall_propagate() {
            DTRACE(std::cout << "overall propagate" << std::endl;);
            clause *conf;
            while(check_propagate_counter()) {
                // using infeasible set to theory propagate literal's value
                propagate_literal_using_infeasible();
                // using valued and assigned literal to check unit clause
                // we do not assign literal in up
                if((conf = unit_propagate()) != nullptr) return conf;
                // using variable to check R_unit clause
                if((conf = real_propagate_clauses()) != nullptr) return conf;
                if((conf = real_propagate_learned()) != nullptr) return conf;
            }
            return nullptr;
        }

        void new_stage() { // record new stage
            DTRACE(std::cout << "new stage" << std::endl;);
            save_new_stage_trail();
            m_scope_stage++;
        }

        hybrid_var pick_branching_var() {
            hybrid_var res;
            while(!m_var_heap.empty()) {
                if(!is_hybrid_assigned(res = m_var_heap.erase_min())) {
                    if(hybrid_is_bool(res)) m_decision_bools.insert(res);
                    DTRACE(
                        if(hybrid_is_arith(res)) {
                            std::cout << "pick branching arith var: " << hybrid2arith(res) << " ";
                            m_display_var(std::cout, hybrid2arith(res));
                        } else {
                            std::cout << "pick branching bool var: " << res;
                        }
                        std::cout << std::endl;
                    );
                    return res;
                }
            }
            DTRACE(std::cout << "pick branching var: " << null_var << std::endl;);
            return null_var;
        }

        /**
          \note we save new stage under two circumstances below:
          1. branch a new arith var
          2. branch a bool var, but last branched var is arith
          \example [x, y, a, b]
          Assume that when propagating b, we meet a conflict
          If we don't insert new stage when branching a, y is in the same stage.
        */
        bool decide() {
            DTRACE(std::cout << "decide" << std::endl;
                std::cout << "curr m_hk: " << m_hk << std::endl;
            );
            if(m_hk != null_var && !is_hybrid_assigned(m_hk)) { // current m_hk may not be assigned due to resolving
                DTRACE(std::cout << "current m_hk is not assigned, choose value" << std::endl;);
                choose_value();
                return false;
            }
            bool last_arith = hybrid_is_arith(m_hk);
            hybrid_var old_hk = m_hk;
            if((m_hk = pick_branching_var()) == null_var) { // var heap is empty, all vars assigned
                check_overall_satisfied();
                return true;
            }
            // 1. branch bool, split previous arith vars
            // 2. arith var
            if((hybrid_is_bool(m_hk) && last_arith) || hybrid_is_arith(m_hk)) new_stage();
            save_branch_trail(old_hk, m_hk);
            m_hybrid_find_stage[m_hk] = m_scope_stage;
            choose_value();
            return false;
        }

        void choose_value() {
            hybrid_is_bool(m_hk) ? decide_literal(literal(m_pure_bool_vars[m_hk], true)) : select_witness();
        }

        void select_witness() {
            var x = hybrid2arith(m_hk);
            SASSERT(!m_ism.is_full(m_infeasible[x]));
            scoped_anum w(m_am);
            m_ism.peek_in_complement(m_infeasible[x], m_is_int[x], w, false);
            if (!m_am.is_rational(w)) m_irrational_assignments++;
            m_assignment.set_core(x, w);
            DTRACE(display_assignment(std::cout);
            );
            save_arith_assignment_trail(x);
            m_hybrid_trail.push_back(m_hk);
            m_arith_trail.push_back(x);
            m_hybrid_assigned_indices[m_hk] = m_hybrid_trail.size() - 1;
            m_arith_unit_atom[x].clear();
            m_arith_unit_clauses[x].clear();
            m_arith_unit_clauses_more_lits[x].clear();
            m_arith_unit_learned[x].clear();
            m_arith_unit_learned_more_lits[x].clear();
            m_newly_unit_arith_clauses[x].clear();
            m_newly_unit_arith_learned[x].clear();
            check_atom_status_using_arith();
            check_clause_status_using_hybrid_var();
            check_learned_status_using_hybrid_var();
        }

        void check_clause_status_using_hybrid_var() {
            display_assignment(std::cout);
            while (m_hybrid_var_clause_prop < m_hybrid_trail.size()) {
                hybrid_var curr_hybrid_var = m_hybrid_trail[m_hybrid_var_clause_prop++];
                vector<clause_var_watcher *> &watches = m_var_watching_clauses[curr_hybrid_var];
                int j = 0, size = watches.size();
                for (int i = 0; i < size; i++) {
                    hybrid_var another_var = watches[i]->get_another_var(curr_hybrid_var);
                    SASSERT(another_var != null_var);
                    unsigned idx = watches[i]->m_clause_index;
                    clause const &cls = *m_clauses[idx];
                    if (is_hybrid_assigned(another_var)) { // clause is all assigned
                        bool is_sat = false;
                        for (literal l : cls) {
                            SASSERT(value(l) != l_undef);
                            if (value(l) == l_true) {
                                is_sat = true;
                                break;
                            }
                        }
                        watches[j++] = watches[i];
                        if (!is_sat) { // conflict clause, this situation should be found when updating the last unassigned var
                        // @date: 2023/09/21
                        // this situation can occur without preprocessing
                        // b1 \/ b2, b1 \/ !b2
                            std::cout << "idx " << idx << std::endl;
                            display(std::cout, cls) << std::endl;
                            conflict_clause = m_clauses[idx];
                            return;
                        }
                    } else { // try to find another unassigned hybrid var
                        nlsat_clause const *cls = m_nlsat_clauses[watches[i]->m_clause_index];
                        bool found_replace = false;
                        for (bool_var b : cls->m_bool_vars) { // loop bool vars first
                            if (b != another_var && b != curr_hybrid_var && !is_hybrid_assigned(b)) {
                                found_replace = true;
                                watches[i]->replace_var(curr_hybrid_var, b);
                                m_var_watching_clauses[b].push_back(watches[i]);
                                break;
                            }
                        }
                        if (!found_replace) { // not found, loop arith vars
                            for (var v : cls->m_vars) {
                                if (arith2hybrid(v) != another_var && arith2hybrid(v) != curr_hybrid_var && !m_assignment.is_assigned(v)) {
                                    found_replace = true;
                                    watches[i]->replace_var(curr_hybrid_var, arith2hybrid(v));
                                    m_var_watching_clauses[arith2hybrid(v)].push_back(watches[i]);
                                    break;
                                }
                            }
                            if (!found_replace) { // unit to another var
                                watches[j++] = watches[i];
                                if (hybrid_is_arith(another_var)) { // arith var
                                    var v = hybrid2arith(another_var);
                                    unsigned idx = watches[i]->m_clause_index;
                                    m_arith_unit_clauses[v].push_back(idx);
                                    m_newly_unit_arith_clauses[v].push_back(idx);
                                    if (m_clauses[idx]->size() > 1) {
                                        m_arith_unit_clauses_more_lits[v].push_back(idx);
                                    }
                                }
                                else { // bool var
                                    // do nothing, since unit to bool var is considered when unit propagating
                                }
                            }
                        }
                    }
                }
                watches.shrink(j);
            }
        }

        void check_learned_status_using_hybrid_var() {
            while(m_hybrid_var_learned_prop < m_hybrid_trail.size()) {
                hybrid_var curr_hybrid_var = m_hybrid_trail[m_hybrid_var_learned_prop++];
                vector<clause_var_watcher*> &watches = m_var_watching_learned[curr_hybrid_var];
                int j = 0, size = watches.size();
                for(int i = 0; i < size; i++) {
                    hybrid_var another_var = watches[i]->get_another_var(curr_hybrid_var);
                    clause const& cls = *m_clauses[watches[i]->m_clause_index];
                    // this clause is totally assigned
                    // note: this situation will take place since current var may not be unit previously
                    // and this may cause a conflict, but we skip
                    if(another_var == null_var || is_hybrid_assigned(another_var)) {
                        watches[j++] = watches[i];
                        continue;
                    } else { // try to find another unassigned hybrid var
                        nlsat_learned const* cls = m_nlsat_learned[watches[i]->m_clause_index];
                        bool found_replace = false;
                        for(bool_var b: cls->m_bool_vars) { // loop bool vars first
                            if(b != another_var && b != curr_hybrid_var && !is_hybrid_assigned(b)) {
                                found_replace = true;
                                watches[i]->replace_var(curr_hybrid_var, b);
                                m_var_watching_learned[b].push_back(watches[i]);
                                break;
                            }
                        }
                        if(!found_replace) { // not found, loop arith vars
                            for(var v: cls->m_arith_vars) {
                                if(arith2hybrid(v) != another_var && arith2hybrid(v) != curr_hybrid_var && !m_assignment.is_assigned(v)) {
                                    found_replace = true;
                                    watches[i]->replace_var(curr_hybrid_var, arith2hybrid(v));
                                    m_var_watching_learned[arith2hybrid(v)].push_back(watches[i]);
                                    break;
                                }
                            }
                            if(!found_replace) { // unit to another var
                                watches[j++] = watches[i];
                                if(hybrid_is_arith(another_var)) { // arith var
                                    var arith_var = hybrid2arith(another_var);
                                    int idx = watches[i]->m_clause_index;
                                    if(check_learned_unit(idx, arith_var)) {
                                        m_arith_unit_learned[arith_var].push_back(idx);
                                        m_newly_unit_arith_learned[arith_var].push_back(idx);
                                        if(m_learned[idx]->size() > 1) {
                                            m_arith_unit_learned_more_lits[arith_var].push_back(idx);
                                        }
                                    }
                                } else { // bool var, unit propagate, just skip
                                    // do nothing
                                }
                            }
                        }
                    }
                }
                watches.shrink(j);
            }
        }

        inline bool satisfy_reduce_situation() const {
            return OPTIONS::enable_reduce;
        }

        inline bool satisfy_rephase_situation() const {
            return OPTIONS::enable_rephase;
        }

        inline bool satisfy_restart_situation() const {
            return OPTIONS::enable_restart;
        }

        /**
           \brief main procedure
        */
        lbool solve() {
            DTRACE(display_clauses(std::cout) << std::endl;);
            DTRACE(std::cout << "start solving..." << std::endl;);
            while(true) {
                DTRACE(display_status(std::cout););
                // we put frontend_conflict checker in while-loop, 
                // since new registered learned clauses may change frontend info (unit clause or real unit clause)
                if(frontend_conflict) {
                    DTRACE(std::cout << "frontend conflict" << std::endl;);
                    return l_false;
                }
                if(conflict_clause == nullptr) { // not found conflict clause when registering learned clauses
                    if((conflict_clause = overall_propagate()) == nullptr) { // consistent
                        DTRACE(std::cout << "consistent" << std::endl;);
                        if(satisfy_reduce_situation()) reduce();
                        else if(satisfy_rephase_situation()) rephase();
                        else if(satisfy_restart_situation()) restart();
                        else if(decide()) return l_true;
                    }
                    // conflict and unsat, learn empty lemma, found conflict in stage and level zero
                    // even if resolve succeeded, we need next turn's overall propagate to detect possible new conflict
                    else if(!resolve(*conflict_clause)) return l_false;
                } 
                // previously found conflict when registering learned clauses
                else if(!resolve(*conflict_clause)) return l_false;
                // conflict exceed
                if (m_conflicts >= m_max_conflicts) return l_undef;
            }
        }

        // TODO: rephase
        void rephase() {

        }

        void reduce() {
            if(m_learned.size() - m_valued_atom_trail.size() >= max_learnts){
                unsigned sz1 = m_learned.size();
                remove_learnt_act();
                unsigned sz2 = m_learned.size();
                double ratio = 100.0 * sz2 / sz1;
                m_learned_deleted += (sz1 - sz2);
            }
        }

        struct reduceDB_lt {
            bool operator()(nlsat_learned const* cls1, nlsat_learned const* cls2) {
                return cls1->m_clause->size() > 2 && 
                    (cls2->m_clause->size() <= 2 || cls1->m_clause->get_activity() < cls2->m_clause->get_activity());
            }
        };

        unsigned_vector     m_learned_indices;

        void remove_learnt_act(){
            if(m_learned.size() <= 10) return;
            double extra_lim = clause_bump / m_learned.size();
            /**
            * Don't delete binary clauses. From the rest, delete clauses from the first half
            * and clauses with activity smaller than 'extra_lim':
            */
           std::sort(m_nlsat_learned.begin(), m_nlsat_learned.end(), reduceDB_lt());
           m_learned_indices.clear();
           m_learned_indices.resize(m_nlsat_learned.size(), null_var);
           unsigned j = 0, sz = m_nlsat_learned.size();
           for(unsigned i = 0; i < m_nlsat_learned.size(); i++){
                unsigned idx = m_nlsat_learned[i]->m_index;
                clause *cls = m_nlsat_learned[i]->m_clause;
               if(cls->size() > 2 && (i < sz / 2 || cls->get_activity() < extra_lim)){
                   del_clause(cls);
                   m_learned_indices[idx] = null_var;
               } else{
                   m_nlsat_learned[j] = m_nlsat_learned[i];
                   m_learned_indices[idx] = j;
                   j++;
               }
           }
           m_nlsat_learned.shrink(j);
           update_learnt_indices();
        }

        void false_all_learned_update() {
            for(auto const & ele: m_var_watching_learned) {
                for(clause_var_watcher *watcher: ele) {
                    watcher->updated = false;
                    watcher->deleted = false;
                }
            }
            for(auto const & ele: m_pos_literal_watching_learned) {
                for(clause_literal_watcher *watcher: ele) {
                    watcher->updated = false;
                    watcher->deleted = false;
                }
            }
            for(auto const & ele: m_neg_literal_watching_learned) {
                for(clause_literal_watcher *watcher: ele) {
                    watcher->updated = false;
                    watcher->deleted = false;
                }
            }

        }
        
        void update_learnt_indices() {
            false_all_learned_update();
            for(hybrid_var v = 0; v < m_var_watching_learned.size(); v++) {
                int j = 0;
                for(int i = 0; i < m_var_watching_learned[v].size(); i++) {
                    clause_var_watcher *watcher = m_var_watching_learned[v][i];
                    // has been deleted, just skip
                    if(watcher == nullptr || watcher->deleted) continue;
                    // has been updated and not deleted, push back
                    if(watcher->updated) m_var_watching_learned[v][j++] = watcher;
                    else { // not updated
                        watcher->updated = true;
                        int origin_idx = watcher->m_clause_index;
                        if(m_learned_indices[origin_idx] == null_var) { // should be deleted
                            watcher->deleted = true;
                            continue;
                        } else { // should not be deleted
                            watcher->m_clause_index = m_learned_indices[origin_idx];
                            m_var_watching_learned[v][j++] = watcher;
                        }
                    }
                }
                m_var_watching_learned[v].shrink(j);
            }
            for(var v = 0; v < num_arith_vars(); v++) {
                int j = 0;
                for(int i = 0; i < m_arith_unit_learned[v].size(); i++) {
                    unsigned origin_idx = m_arith_unit_learned[v][i];
                    if(m_learned_indices[origin_idx] == null_var) { // should delete
                        continue;
                    } else {
                        m_arith_unit_learned[v][j++] = m_learned_indices[origin_idx];
                    }
                }
                m_arith_unit_learned[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_arith_unit_learned_more_lits[v].size(); i++) {
                    unsigned origin_idx = m_arith_unit_learned_more_lits[v][i];
                    if(m_learned_indices[origin_idx] == null_var) {
                        continue;
                    } else {
                        m_arith_unit_clauses_more_lits[v][j++] = m_learned_indices[origin_idx];
                    }
                }
                m_arith_unit_learned_more_lits[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_newly_unit_arith_learned[v].size(); i++) {
                    unsigned origin_idx = m_newly_unit_arith_learned[v][i];
                    if(m_learned_indices[origin_idx] == null_var) {
                        continue;
                    } else {
                        m_newly_unit_arith_learned[v][j++] = m_learned_indices[origin_idx];
                    }
                }
                m_newly_unit_arith_learned[v].shrink(j);
            }
            for(bool_var b = 0; b < m_atoms.size(); b++) {
                int j = 0;
                for(int i = 0; i < m_pos_literal_watching_learned[b].size(); i++) {
                    clause_literal_watcher *watcher = m_pos_literal_watching_learned[b][i];
                    // watcher has been deleted, just skip
                    if(watcher == nullptr || watcher->deleted) continue;
                    // watcher has been updated, push back
                    if(watcher->updated) m_pos_literal_watching_learned[b][j++] = watcher;
                    else { // not updated
                        watcher->updated = true;
                        int origin_idx = watcher->m_clause_index;
                        if(m_learned_indices[origin_idx] == null_var) { // should be deleted
                            watcher->deleted = true;
                            continue;
                        } else { // should not be deleted
                            watcher->m_clause_index = m_learned_indices[origin_idx];
                            m_pos_literal_watching_learned[b][j++] = watcher;
                        }
                    }
                }
                m_pos_literal_watching_learned[b].shrink(j);
                j = 0;
                for(int i = 0; i < m_neg_literal_watching_learned[b].size(); i++) {
                    clause_literal_watcher *watcher = m_neg_literal_watching_learned[b][i];
                    // watcher has been deleted, just skip
                    if(watcher == nullptr || watcher->deleted) continue;
                    // watcher has been updated, push back
                    if(watcher->updated) m_neg_literal_watching_learned[b][j++] = watcher;
                    else { // not updated
                        watcher->updated = true;
                        int origin_idx = watcher->m_clause_index;
                        if(m_learned_indices[origin_idx] == null_var) { // should be deleted
                            watcher->deleted = true;
                            continue;
                        } else { // should not be deleted
                            watcher->m_clause_index = m_learned_indices[origin_idx];
                            m_neg_literal_watching_learned[b][j++] = watcher;
                        }
                    }
                }
                m_neg_literal_watching_learned[b].shrink(j);
            }
            for(bool_var b = 0; b < m_atoms.size(); b++) {
                unsigned idx = m_frontend_unit_indices[b];
                if(idx == null_var || idx % 2 == 0) continue;
                unsigned learned_idx = idx / 2;
                m_frontend_unit_indices[b] = m_learned_indices[learned_idx] == null_var ? // delete or not
                                            null_var : encode_unit_indices(m_learned_indices[learned_idx], true);
            }
        }

        static double luby(double y, int x) {
            int size, seq;
            for(size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);
            while(size-1 != x){
                size = (size-1)>>1;
                seq--;
                x = x % size;
            }
            return std::pow(y, seq);
        }

        void init_restart_options() {
            m_restarts = 0;
            double rest_base = OPTIONS::luby_restart ? luby(OPTIONS::restart_inc, m_restarts) : std::pow(OPTIONS::restart_inc, m_restarts);
            m_restart_threshold = rest_base * OPTIONS::restart_init;
        }

        lbool search_check() {
            lbool r = l_undef;
            init_restart_options();
            while (true) { // branch and bound used in nia    
                r = solve();
                if (r != l_true) return r;
                // nra done

                // branch and bound for nia instances
                vector<std::pair<var, rational>> bounds;                
                for (var x = 0; x < num_arith_vars(); x++) {
                    if (m_is_int[x] && m_assignment.is_assigned(x) && !m_am.is_int(m_assignment.value(x))) {
                        scoped_anum v(m_am), vlo(m_am);
                        v = m_assignment.value(x);
                        rational lo;
                        m_am.int_lt(v, vlo);
                        if (!m_am.is_int(vlo)) 
                            continue;
                        m_am.to_rational(vlo, lo);
                        // derive tight bounds.
                        while (true) {
                            lo++;
                            if (!m_am.gt(v, lo.to_mpq())) { lo--; break; }
                        }
                        bounds.push_back(std::make_pair(x, lo));
                    }
                }
                if (bounds.empty()) break;
                init_search();
                for (auto const& b : bounds) {
                    var x = b.first;
                    rational lo = b.second;
                    rational hi = lo + 1; // rational::one();
                    bool is_even = false;                        
                    polynomial_ref p(m_pm);
                    rational one(1);
                    m_lemma.reset();
                    p = m_pm.mk_linear(1, &one, &x, -lo);
                    poly* p1 = p.get();
                    m_lemma.push_back(~mk_ineq_literal(atom::GT, 1, &p1, &is_even));
                    p = m_pm.mk_linear(1, &one, &x, -hi);
                    poly* p2 = p.get();
                    m_lemma.push_back(~mk_ineq_literal(atom::LT, 1, &p2, &is_even));
                    // perform branch and bound
                    clause * cls = mk_clause(m_lemma.size(), m_lemma.data(), false, nullptr);
                }
            }
            return r;
        }

        void register_nlsat_structures() {
            register_nlsat_vars();
            register_nlsat_atoms();
            register_nlsat_clauses();
        }

        void register_nlsat_vars() {
            for(bool_var b = 0; b < m_atoms.size(); b++) {
                if(m_atoms[b] == nullptr) { // pure bool var
                    register_nlsat_bvar(b);
                }
            }
            for(var v = 0; v < m_is_int.size(); v++) {
                register_nlsat_avar(v);
            }
            DTRACE(std::cout << "register vars done" << std::endl;);
        }

        void register_nlsat_atoms() {
            for(bool_var b = 0; b < m_atoms.size(); b++) {
                if(m_atoms[b] != nullptr) {
                    register_nlsat_atom(b);
                }
            }
            DTRACE(std::cout << "register atoms done" << std::endl;);
        }

        void register_nlsat_clauses() {
            for(unsigned i = 0; i < m_clauses.size(); i++) {
                register_nlsat_clause(i);
            }
            DTRACE(std::cout << "register clauses done" << std::endl;);
        }

        void register_nlsat_avar(var x) {
            m_num_hybrid_vars++;
            m_hybrid_assigned_indices.setx(arith2hybrid(x), null_var, null_var);
            m_hybrid_find_stage.setx(arith2hybrid(x), null_var, null_var);
            m_hybrid_activity.setx(arith2hybrid(x), 0, 0);
            m_var_atoms.enlarge(x, var_vector(0));
            m_var_clauses.enlarge(x, var_vector(0));
            m_var_learned.enlarge(x, var_vector(0));
            m_static_unit_atom.enlarge(x, var_vector(0));
            m_var_watching_atoms.enlarge(x, vector<atom_var_watcher*>(0));
            m_var_watching_clauses.enlarge(arith2hybrid(x), vector<clause_var_watcher*>(0));
            m_var_watching_learned.enlarge(arith2hybrid(x), vector<clause_var_watcher*>(0));
            m_var_atom_infeasible_set.enlarge(x, vector<interval_set_bool>(m_atoms.size()));
            m_var_clause_infeasible_set.enlarge(x, vector<interval_set_bool>(m_clauses.size()));
            m_var_learned_infeasible_set.enlarge(x, vector<interval_set_bool>(m_learned.size()));
            m_arith_unit_atom.enlarge(x, var_vector(0));
            m_arith_unit_clauses.enlarge(x, var_vector(0));
            m_arith_unit_clauses_more_lits.enlarge(x, var_vector(0));
            m_arith_unit_learned.enlarge(x, var_vector(0));
            m_arith_unit_learned_more_lits.enlarge(x, var_vector(0));
            m_newly_unit_arith_clauses.enlarge(x, var_vector(0));
            m_newly_unit_arith_learned.enlarge(x, var_vector(0));
            m_frontend_infeasible.enlarge(x, nullptr);
        }

        void register_nlsat_bvar(bool_var b) {
            m_num_hybrid_vars++;
            m_assigned_atom_indices.setx(b, null_var, null_var);
            m_hybrid_assigned_indices.setx(b, null_var, null_var);
            m_hybrid_find_stage.setx(b, null_var, null_var);
            m_hybrid_activity.setx(b, 0, 0);
            m_frontend_bvalues.enlarge(b, l_undef);
            m_frontend_unit_indices.enlarge(b, null_var);
            m_frontend_used.enlarge(b, false);
            m_atom_unit_clauses.enlarge(b, null_var);
            m_atom_unit_learned.enlarge(b, null_var);
            m_bool_clauses.enlarge(b, var_vector(0));
            m_bool_learned.enlarge(b, var_vector(0));
            m_nlsat_atoms.enlarge(b, nullptr);
            m_nlsat_atoms[b] = new nlsat_atom(b, nullptr, var_table());
            m_var_watching_clauses.enlarge(b, vector<clause_var_watcher*>(0));
            m_var_watching_learned.enlarge(b, vector<clause_var_watcher*>(0));
            m_pos_literal_watching_clauses.enlarge(b, vector<clause_literal_watcher*>(0));
            m_pos_literal_watching_learned.enlarge(b, vector<clause_literal_watcher*>(0));
            m_neg_literal_watching_clauses.enlarge(b, vector<clause_literal_watcher*>(0));
            m_neg_literal_watching_learned.enlarge(b, vector<clause_literal_watcher*>(0));
            if(!m_pure_bool_vars.contains(b)) {
                m_pure_bool_vars.push_back(b);
                m_pure_bool_convert.enlarge(b, null_var);
                m_pure_bool_convert[b] = m_pure_bool_vars.size() - 1;
            }
        }

         void register_nlsat_atom(bool_var b) {
            m_nlsat_atoms.enlarge(b, nullptr);
            m_assigned_atom_indices.enlarge(b, null_var);
            var_table vars;
            collect_atom_vars(m_atoms[b], vars);
            m_nlsat_atoms[b] = new nlsat_atom(b, m_atoms[b], vars);
            m_atom_unit_clauses.enlarge(b, null_var);
            m_atom_unit_learned.enlarge(b, null_var);
            m_pos_literal_watching_clauses.enlarge(b, vector<clause_literal_watcher*>(0));
            m_pos_literal_watching_learned.enlarge(b, vector<clause_literal_watcher*>(0));
            m_neg_literal_watching_clauses.enlarge(b, vector<clause_literal_watcher*>(0));
            m_neg_literal_watching_learned.enlarge(b, vector<clause_literal_watcher*>(0));
            m_frontend_bvalues.enlarge(b, l_undef);
            m_frontend_unit_indices.enlarge(b, null_var);
            m_frontend_used.enlarge(b, null_var);
            for(var v: vars) {
                m_var_atoms.enlarge(v, unsigned_vector(0));
                m_var_atoms[v].push_back(b);
            }
            for(var v = 0; v < m_var_atom_infeasible_set.size(); v++) {
                m_var_atom_infeasible_set[v].enlarge(b, std::make_pair(false, nullptr));
            }
            set_atom_arith_watcher(b);
        }

        void register_nlsat_clause(unsigned idx) {
            clause * cls = m_clauses[idx];
            std::sort(cls->begin(), cls->end(), lit_lt(*this));
            m_nlsat_clauses.enlarge(idx, nullptr);
            var_table avars; bool_var_table bvars;
            collect_clause_arith_and_bool_vars(m_clauses[idx], avars, bvars);
            m_nlsat_clauses[idx] = new nlsat_clause(idx, m_clauses[idx], avars, bvars);
            for(bool_var bv: bvars) {
                m_bool_clauses.enlarge(bv, unsigned_vector(0));
                m_bool_clauses[bv].push_back(idx);
            }
            for(var av: avars) {
                m_var_clauses.enlarge(av, unsigned_vector(0));
                m_var_clauses[av].push_back(idx);
            }
            for(var v = 0; v < m_var_clause_infeasible_set.size(); v++) {
                m_var_clause_infeasible_set[v].enlarge(idx, std::make_pair(false, nullptr));
            }
            bool deleted;
            set_clause_literal_watcher(idx, deleted);
            if(!deleted) {
                set_clause_var_watcher(idx);
            }
        }

        void collect_learned_arith_and_bool_vars(clause const *cls, bool_var_table &bvars, var_table &avars, var_table &rpvars) {
            bvars.reset(); avars.reset(); rpvars.reset();
            for(literal l: *cls) {
                if(m_atoms[l.var()] == nullptr) {
                    bvars.insert_if_not_there(m_pure_bool_convert[l.var()]);
                } else {
                    var_table curr_vars;
                    collect_atom_vars(m_atoms[l.var()], curr_vars);
                    for(var v: curr_vars) {
                        avars.insert_if_not_there(v);
                    }
                    if(m_atoms[l.var()]->is_root_atom()) {
                        root_atom *ra = to_root_atom(m_atoms[l.var()]);
                        var_vector curr_vars;
                        m_pm.vars(ra->p(), curr_vars);
                        for(var v: curr_vars) {
                            if(v != ra->x()) {
                                rpvars.insert_if_not_there(v);
                            }
                        }
                    }
                }
            }
        }

        void register_nlsat_learned(unsigned idx) {
            m_nlsat_learned.enlarge(idx, nullptr);
            var_table avars, rpvars; bool_var_table bvars;
            collect_learned_arith_and_bool_vars(m_learned[idx], bvars, avars, rpvars);
            m_nlsat_learned[idx] = new nlsat_learned(idx, m_learned[idx], bvars, avars, rpvars);
            for(var av: avars) {
                m_var_learned.enlarge(av, unsigned_vector(0));
                m_var_learned[av].push_back(idx);
            }
            for(bool_var bv: bvars) {
                m_bool_learned.enlarge(bv, unsigned_vector(0));
                m_bool_learned[bv].push_back(idx);
            }
            for(var v = 0; v < m_var_learned_infeasible_set.size(); v++) {
                m_var_learned_infeasible_set[v].enlarge(idx, std::make_pair(false, nullptr));
            }
            set_learned_literal_watcher(idx);
            set_learned_var_watcher(idx);
        }

        void clear_assignment() {
            for (unsigned i = 0; i < m_bvalues.size(); i++) {
                m_bvalues[i] = l_undef;
            }
            m_assignment.reset();
        }

        void clear_nlsat_structures() {
            clear_nlsat_vars();
            clear_nlsat_atoms();
            clear_nlsat_clauses();
            clear_nlsat_learned();
            clear_nlsat_trails();
            clear_frontend_info();
            conflict_clause = nullptr;
            frontend_conflict = false;
            generate_during_process = false;
        }

        void clear_nlsat_vars() {
            m_num_hybrid_vars = 0;
            m_pure_bool_convert.clear();
            m_pure_bool_vars.clear();
            m_hybrid_assigned_indices.clear();
            m_hybrid_find_stage.clear();
            m_hybrid_activity.clear();
            m_bool_clauses.clear();
            m_bool_learned.clear();
            m_var_heap.clear();
            m_var_atoms.clear();
            m_var_clauses.clear();
            m_var_learned.clear();
            m_static_unit_atom.clear();
            m_var_watching_atoms.clear();
            m_var_watching_clauses.clear();
            m_var_watching_learned.clear();
            m_var_atom_infeasible_set.clear();
            m_var_clause_infeasible_set.clear();
            m_var_learned_infeasible_set.clear();
            m_arith_unit_atom.clear();
            m_arith_unit_clauses.clear();
            m_arith_unit_clauses_more_lits.clear();
            m_arith_unit_learned.clear();
            m_arith_unit_learned_more_lits.clear();
            m_newly_unit_arith_clauses.clear();
            m_newly_unit_arith_learned.clear();
            m_decision_bools.reset();
            m_arith_level.clear();
            m_var_max_level.clear();
        }

        void clear_nlsat_atoms() {
            m_nlsat_atoms.clear();
            m_assigned_atom_indices.clear();
            m_atom_unit_clauses.clear();
            m_atom_unit_learned.clear();
            m_neg_literal_watching_clauses.clear();
            m_pos_literal_watching_clauses.clear();
            m_neg_literal_watching_learned.clear();
            m_pos_literal_watching_learned.clear();
        }

        void clear_nlsat_clauses() {
            m_nlsat_clauses.clear();
        }

        void clear_nlsat_learned() {
            m_nlsat_learned.clear();
        }

        void clear_nlsat_trails() {
            m_bool_trail.clear();
            m_arith_trail.clear();
            m_hybrid_trail.clear();
            m_valued_atom_table.reset();
            m_valued_atom_trail.clear();
            m_infeasible_var_trail.clear();
            m_atom_prop = 0;
            m_arith_atom_prop = 0;
            m_infeasible_prop = 0;
            m_hybrid_var_clause_prop = 0;
            m_hybrid_var_learned_prop = 0;
        }

        void clear_frontend_info() {
            m_frontend_bvalues.clear();
            m_frontend_infeasible.clear();
        }

        void del_nlsat_atom(bool_var b) {
            DTRACE(std::cout << "delete atom: " << b << std::endl;);
            SASSERT(b < m_nlsat_atoms.size());
            m_atom_unit_clauses[b] = null_var;
            m_atom_unit_learned[b] = null_var;
            m_pos_literal_watching_clauses[b].clear();
            m_neg_literal_watching_clauses[b].clear();
            m_pos_literal_watching_learned[b].clear();
            m_neg_literal_watching_learned[b].clear();
            if(m_nlsat_atoms[b]->m_vars.size() == 1) {
                var v = *m_nlsat_atoms[b]->m_vars.begin();
                m_static_unit_atom[v].erase(b);
            }
            int j;
            if(m_nlsat_atoms[b]->m_var_watcher != nullptr) {
                var v1 = m_nlsat_atoms[b]->m_var_watcher->v1, v2 = m_nlsat_atoms[b]->m_var_watcher->v2;
                std::cout << "v1: " << v1 << " , v2: " << v2 << std::endl;
                var_vector vec;
                vec.push_back(v1); vec.push_back(v2);
                for(var v: vec) {
                    std::cout << "v: " << v << std::endl;
                    j = 0;
                    for(int i = 0; i < m_var_watching_atoms[v].size(); i++) {
                        if(m_var_watching_atoms[v][i]->m_atom_index != b) {
                            m_var_watching_atoms[v][j++] = m_var_watching_atoms[v][i];
                        }
                    }
                    m_var_watching_atoms[v].shrink(j);
                }
            }
            for (var v: m_nlsat_atoms[b]->m_vars) {
                j = 0;
                for(int i = 0; i < m_arith_unit_atom[v].size(); i++) {
                    if(m_arith_unit_atom[v][i] != b) {
                        m_arith_unit_atom[v][j++] = m_arith_unit_atom[v][i];
                    }
                }
                m_arith_unit_atom[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_var_atoms[v].size(); i++) {
                    if(m_var_atoms[v][i] != b) {
                        m_var_atoms[v][j++] = m_var_atoms[v][i];
                    }
                }    
                m_var_atoms[v].shrink(j);
                m_var_atom_infeasible_set[v][b] = std::make_pair(false, nullptr);
            }
            m_nlsat_atoms[b] = nullptr;
        }

        void del_nlsat_clause(unsigned id) {
            SASSERT(id < m_nlsat_clauses.size());
            int j;
            if(m_nlsat_clauses[id]->m_var_watcher != nullptr) { // chaneg clause var watcher
                hybrid_var v1 = m_nlsat_clauses[id]->m_var_watcher->v1, v2 = m_nlsat_clauses[id]->m_var_watcher->v2;
                var_vector vec;
                vec.push_back(v1); vec.push_back(v2);
                for(hybrid_var v: vec) {
                    j = 0;
                    for(int i = 0; i < m_var_watching_clauses[v1].size(); i++) {
                        if(m_var_watching_clauses[v][i]->m_clause_index != id) {
                            m_var_watching_clauses[v][j++] = m_var_watching_clauses[v][i];
                        }
                    }
                    m_var_watching_clauses[v].shrink(j);
                }
            }
            if(m_clauses[id]->size() == 1) {
                literal l = (*m_clauses[id])[0];
                m_atom_unit_clauses[l.var()] = null_var;
            }
            if(m_nlsat_clauses[id]->m_atom_watcher != nullptr) { // change clause literal watcher
                int i1 = m_nlsat_clauses[id]->m_atom_watcher->l1, i2 = m_nlsat_clauses[id]->m_atom_watcher->l2;
                int indices[2] = {i1, i2};
                for(int k = 0; k < 2; k++) {
                    int index = indices[k];
                    j = 0;
                    SASSERT(index != 0);
                    if(index > 0) {
                        for(int i = 0; i < m_pos_literal_watching_clauses[index].size(); i++) {
                            if(m_pos_literal_watching_clauses[index][i]->m_clause_index != id) {
                                m_pos_literal_watching_clauses[index][j++] = m_pos_literal_watching_clauses[index][i];
                            }
                        }
                        m_pos_literal_watching_clauses[index].shrink(j);
                    } else {
                        for(int i = 0; i < m_neg_literal_watching_clauses[-index].size(); i++) {
                            if(m_neg_literal_watching_clauses[-index][i]->m_clause_index != id) {
                                m_neg_literal_watching_clauses[-index][j++] = m_neg_literal_watching_clauses[-index][i];
                            }
                        }
                        m_neg_literal_watching_clauses[-index].shrink(j);
                    }
                }
            }
            for(var v: m_nlsat_clauses[id]->m_vars) { // change var's unit clause
                j = 0;
                for(int i = 0; i < m_arith_unit_clauses[v].size(); i++) {
                    if(m_arith_unit_clauses[v][i] != id) {
                        m_arith_unit_clauses[v][j++] = m_arith_unit_clauses[v][i];
                    }
                }
                m_arith_unit_clauses[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_arith_unit_clauses_more_lits[v].size(); i++) {
                    if(m_arith_unit_clauses_more_lits[v][i] != id) {
                        m_arith_unit_clauses_more_lits[v][j++] = m_arith_unit_clauses_more_lits[v][i];
                    }
                }
                m_arith_unit_clauses_more_lits[v].shrink(j);
                j = 0;
                for (int i = 0; i < m_newly_unit_arith_clauses[v].size(); i++) {
                    if(m_newly_unit_arith_clauses[v][i] != id) {
                        m_newly_unit_arith_clauses[v][j++] = m_newly_unit_arith_clauses[v][i];
                    }
                }
                m_newly_unit_arith_clauses[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_var_clauses[v].size(); i++) {
                    if(m_var_clauses[v][i] != id) {
                        m_var_clauses[v][j++] = m_var_clauses[v][i];
                    }
                }
                m_var_clauses[v].shrink(j);
                m_var_clause_infeasible_set[v][id] = std::make_pair(false, nullptr);
            }
            for(bool_var bv: m_nlsat_clauses[id]->m_bool_vars) {
                j = 0;
                for(int i = 0; i < m_bool_clauses[bv].size(); i++) {
                    if(m_bool_clauses[bv][i] != id) {
                        m_bool_clauses[bv][j++] = m_bool_clauses[bv][i];
                    }
                }
                m_bool_clauses[bv].shrink(j);
            }
            m_nlsat_clauses[id] = nullptr;
        }

        void del_nlsat_learned(unsigned id) {
            SASSERT(id < m_nlsat_learned.size());
            int j;
            if(m_nlsat_learned[id]->m_var_watcher != nullptr) { // change learned var watcher
                hybrid_var v1 = m_nlsat_learned[id]->m_var_watcher->v1, v2 = m_nlsat_learned[id]->m_var_watcher->v2;
                var_vector vec;
                vec.push_back(v1);
                vec.push_back(v2);
                for(hybrid_var v: vec) {
                    j = 0;
                    for(int i = 0; i < m_var_watching_learned[v].size(); i++) {
                        if(m_var_watching_learned[v][i]->m_clause_index != id) {
                            m_var_watching_learned[v][j++] = m_var_watching_learned[v][i];
                        }
                    }
                    m_var_watching_learned.shrink(j);
                }
            }
            if(m_learned[id]->size() == 1) {
                literal l = (*m_learned[id])[0];
                m_atom_unit_learned[l.var()] = null_var;
            }
            if(m_nlsat_learned[id]->m_atom_watcher != nullptr) { // change learned literal watcher
                int i1 = m_nlsat_learned[id]->m_atom_watcher->l1, i2 = m_nlsat_learned[id]->m_atom_watcher->l2;
                int indices[2] = {i1, i2};
                for(int k = 0; k < 2; k++) {
                    int index = indices[k];
                    j = 0;
                    SASSERT(index != 0);
                    if(index > 0) {
                        for(int i = 0; i < m_pos_literal_watching_learned[index].size(); i++) {
                            if(m_pos_literal_watching_learned[index][i]->m_clause_index != id) {
                                m_pos_literal_watching_learned[index][j++] = m_pos_literal_watching_learned[index][i];
                            }
                        }
                        m_pos_literal_watching_learned[index].shrink(j);
                    } else {
                        for(int i = 0; i < m_neg_literal_watching_learned[-index].size(); i++) {
                            if(m_neg_literal_watching_learned[-index][i]->m_clause_index != id) {
                                m_neg_literal_watching_learned[-index][j++] = m_neg_literal_watching_learned[-index][i];
                            }
                        }
                        m_neg_literal_watching_learned[-index].shrink(j);
                    }
                }
            }
            for(bool_var b: m_nlsat_learned[id]->m_bool_vars) {
                int j = 0;
                for(int i = 0; i < m_bool_learned[b].size(); i++) {
                    if(m_bool_learned[b][i] != id) {
                        m_bool_learned[b][j++] = m_bool_learned[b][i];
                    }
                }
                m_bool_learned[b].shrink(j);
            }
            for(var v: m_nlsat_learned[id]->m_arith_vars) {
                int j = 0;
                for(int i = 0; i < m_arith_unit_learned[v].size(); i++) {
                    if(m_arith_unit_learned[v][i] != id) {
                        m_arith_unit_learned[v][j++] = m_arith_unit_learned[v][i];
                    }
                }
                m_arith_unit_learned[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_arith_unit_learned_more_lits[v].size(); i++) {
                    if(m_arith_unit_learned_more_lits[v][i] != id) {
                        m_arith_unit_learned_more_lits[v][j++] = m_arith_unit_learned_more_lits[v][i];
                    }
                }
                m_arith_unit_learned_more_lits[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_newly_unit_arith_learned[v].size(); i++) {
                    if(m_newly_unit_arith_learned[v][i] != id) {
                        m_newly_unit_arith_learned[v][j++] = m_newly_unit_arith_learned[v][i];
                    }
                }
                m_newly_unit_arith_learned[v].shrink(j);
                j = 0;
                for(int i = 0; i < m_var_learned[v].size(); i++) {
                    if(m_var_learned[v][i] != id) {
                        m_var_learned[v][j++] = m_var_learned[v][i];
                    }
                }
                m_var_learned[v].shrink(j);
                m_var_learned_infeasible_set[v][id] = std::make_pair(false, nullptr);
            }
            m_nlsat_learned[id] = nullptr;
        }

        void collect_atom_vars(atom const *a, var_table &vars) {
            vars.reset();
            if(a == nullptr) {
                return;
            } else if(a->is_ineq_atom()) {
                collect_ineq_vars(to_ineq_atom(a), vars);
            } else {
                collect_root_vars(to_root_atom(a), vars);
            }
        }

        void collect_ineq_vars(ineq_atom const *a, var_table &vars) {
            if(a == nullptr) {
                return;
            }
            for(unsigned i = 0; i < a->size(); i++) {
                var_vector curr_vars;
                m_pm.vars(a->p(i), curr_vars);
                for(var v: curr_vars) {
                    vars.insert_if_not_there(v);
                }
            }
        }

        void collect_root_vars(root_atom const *a, var_table &vars) {
            if(a == nullptr) {
                return;
            }
            var_vector curr_vars;
            m_pm.vars(a->p(), curr_vars);
            for(var v: curr_vars) {
                vars.insert_if_not_there(v);
            }
            vars.insert_if_not_there(a->x());
        }

        void collect_clause_arith_and_bool_vars(clause const *cls, var_table &avars, bool_var_table &bvars) {
            avars.reset(); bvars.reset();
            for(literal l: *cls) {
                bool_var b = l.var();
                if(m_atoms[b] == nullptr) {
                    bvars.insert_if_not_there(m_pure_bool_convert[b]);
                } else {
                    nlsat_atom const *curr_atom = m_nlsat_atoms[b];
                    for(var v: curr_atom->m_vars) {
                        avars.insert_if_not_there(v);
                    }
                }
            }
        }

        void get_atom_last_assigned_two_vars(unsigned idx, var &v1, var &v2) {
            unsigned max1 = null_var, max2 = null_var;
            for(var x: m_nlsat_atoms[idx]->m_vars) {
                unsigned index = m_hybrid_assigned_indices[arith2hybrid(x)];
                if(index == null_var) {
                    continue;
                }
                if(max1 == null_var) {
                    max1 = index;
                    v1 = x;
                } else if(max2 == null_var) {
                    if(index >= max1) {
                        max2 = max1;
                        v2 = v1;
                        max1 = index;
                        v1 = x;
                    } else {
                        max2 = index;
                        v2 = x;
                    }
                } else {
                    if(index >= max1) {
                        max2 = max1;
                        v2 = v1;
                        max1 = index;
                        v1 = x;
                    } else if(index >= max2 && index < max1) {
                        max2 = index;
                        v2 = x;
                    } else {

                    }
                }
            }
        }

        void get_atom_last_assigned_one_var(unsigned idx, var &v) {
            unsigned max_i = null_var;
            for(var x: m_nlsat_atoms[idx]->m_vars) {
                unsigned index = m_hybrid_assigned_indices[arith2hybrid(x)];
                if(index == null_var) {
                    continue;
                }
                if(max_i == null_var) {
                    max_i = index;
                    v = x;
                } else if(index > max_i) {
                    max_i = index;
                    v = x;
                }
            }
        }

        void set_atom_arith_watcher(unsigned idx) {
            nlsat_atom const *curr_atom = m_nlsat_atoms[idx];
            if(curr_atom->m_vars.empty()) { // bool literal
                return;
            } else if(curr_atom->m_vars.size() == 1) { // unit arith atom
                auto it = curr_atom->m_vars.begin();
                var v = *it;
                m_static_unit_atom[v].push_back(idx);
                if(!m_assignment.is_assigned(v)) {
                    insert_unit_atom(idx, v);
                }
            } else { // atom with arith vars >= 2
                SASSERT(curr_atom->m_vars.size() >= 2);
                var v1 = null_var, v2 = null_var;
                for(var v: curr_atom->m_vars) {
                    if(!m_assignment.is_assigned(v)) {
                        if(v1 == null_var) v1 = v;
                        else if(v2 == null_var) v2 = v;
                        else break;
                    }
                }
                atom_var_watcher *new_watcher;
                if(v1 == null_var && v2 == null_var) { // all assigned
                    get_atom_last_assigned_two_vars(idx, v1, v2);
                } else if(v1 != null_var && v2 == null_var) { // only v1 unassigned
                    get_atom_last_assigned_one_var(idx, v2);
                    if(m_atoms[idx]->is_ineq_atom() || to_root_atom(m_atoms[idx])->x() == v1) {
                        insert_unit_atom(idx, v1);
                    }
                } else if(v1 != null_var && v2 != null_var) { // both unassigned
                    // do nothing
                } else {
                    UNREACHABLE();
                }
                new_watcher = new atom_var_watcher(idx, v1, v2);
                m_var_watching_atoms[v1].push_back(new_watcher);
                m_var_watching_atoms[v2].push_back(new_watcher);
                m_nlsat_atoms[idx]->m_var_watcher = new_watcher;
            }
        }

        void propagate_atom(unsigned idx, var unit_v) {
            if(unit_v != null_var) {
                interval_set_ref curr_st(m_ism);
                curr_st = get_atom_infeasible_set(idx, unit_v, false);
                if (m_ism.is_empty(curr_st))  R_propagate(literal(idx, false), nullptr);
                else if (m_ism.is_full(curr_st)) R_propagate(literal(idx, true), nullptr);
                else if (m_ism.subset(curr_st, m_infeasible[unit_v])) R_propagate(literal(idx, false), m_infeasible[unit_v]);
                else {
                    interval_set_ref tmp(m_ism);
                    tmp = m_ism.mk_union(curr_st, m_infeasible[unit_v]);
                    if (m_ism.is_full(tmp)) R_propagate(literal(idx, true), tmp, false);
                }
            }
        }

        void update_infeasible_cache_using_bool(bool_var b) {
            for(unsigned idx: m_bool_clauses[b]) {
                for(var v: m_nlsat_clauses[idx]->m_vars) {
                    m_var_clause_infeasible_set[v][idx].first = false;
                }
            }
            for(unsigned idx: m_bool_learned[b]) {
                for(var v: m_nlsat_learned[idx]->m_arith_vars) {
                    m_var_learned_infeasible_set[v][idx].first = false;
                }
            }
        }

        void update_infeasible_cache_using_arith(var v) {
            for(unsigned idx: m_var_clauses[v]) {
                clause const &curr_clause = *m_clauses[idx];
                for(literal l: curr_clause) {
                    if(m_nlsat_atoms[l.var()]->m_vars.contains(v)) {
                        for(var nv: m_nlsat_atoms[l.var()]->m_vars) {
                            if(nv != v) {
                                m_var_atom_infeasible_set[nv][l.var()].first = false;
                                m_var_clause_infeasible_set[nv][idx].first = false;
                            }
                        }
                    }
                }
            }
            for(unsigned idx: m_var_learned[v]) {
                clause const &curr_clause = *m_learned[idx];
                for(literal l: curr_clause) {
                    if(m_nlsat_atoms[l.var()]->m_vars.contains(v)) {
                        for(var nv: m_nlsat_atoms[l.var()]->m_vars) {
                            if(nv != v) {
                                m_var_atom_infeasible_set[nv][l.var()].first = false;
                                m_var_learned_infeasible_set[nv][idx].first = false;
                            }
                        }
                    }
                }
            }
        }

        interval_set* get_atom_infeasible_set(int idx, var v, bool sign) {
            if(m_var_atom_infeasible_set[v][idx].first) {
                return sign ? m_ism.mk_complement(m_var_atom_infeasible_set[v][idx].second) : m_var_atom_infeasible_set[v][idx].second;
            } else {
                interval_set_ref curr_st(m_ism);
                curr_st = m_evaluator.infeasible_intervals(m_atoms[idx], false, nullptr, v);
                if(curr_st != nullptr) {
                    m_ism.inc_ref(curr_st);
                }
                m_var_atom_infeasible_set[v][idx] = std::make_pair(true, curr_st);
                return sign ? m_ism.mk_complement(curr_st) : curr_st;
            }
        }

        // assert unit to v
        interval_set* get_clause_infeasible_set(int idx, var v) {
            if(m_var_clause_infeasible_set[v][idx].first) { // cached before
                return m_var_clause_infeasible_set[v][idx].second;
            } else {
                interval_set_ref curr_st(m_ism);
                interval_set_ref atom_st(m_ism);
                curr_st = m_ism.mk_full();
                for(literal l: *m_clauses[idx]) {
                    if(m_nlsat_atoms[l.var()]->m_vars.contains(v)) {
                        atom_st = get_atom_infeasible_set(l.var(), v, l.sign());
                        curr_st = m_ism.mk_intersection(curr_st, atom_st);
                    } else {
                        lbool v = value(l);
                        SASSERT(v != l_undef);
                        if(v == l_true) {
                            return nullptr;
                        } else if(v == l_false) {
                            continue;
                        } else {
                            UNREACHABLE();
                        }
                    }
                }
                if(curr_st != nullptr) {
                    m_ism.inc_ref(curr_st);
                }
                m_var_clause_infeasible_set[v][idx] = std::make_pair(true, curr_st);
                return curr_st;
            }
        }

        interval_set* get_learned_infeasible_set(int idx, var v) {
            if(m_var_learned_infeasible_set[v][idx].first) { // cached before
                return m_var_learned_infeasible_set[v][idx].second;
            } else { // not cache
                interval_set_ref curr_st(m_ism), atom_st(m_ism);
                curr_st = m_ism.mk_full();
                for(literal l: *m_learned[idx]) {
                    if(m_nlsat_atoms[l.var()]->m_vars.contains(v)) {
                        atom_st = get_atom_infeasible_set(l.var(), v, l.sign());
                        curr_st = m_ism.mk_intersection(curr_st, atom_st);
                    } else {
                        lbool v = value(l);
                        SASSERT(v != l_undef);
                        if(v == l_true) {
                            return nullptr;
                        } else if(v == l_false) {
                            continue;
                        } else {
                            UNREACHABLE();
                        }
                    }
                }
                if(curr_st != nullptr) {
                    m_ism.inc_ref(curr_st);
                }
                m_var_learned_infeasible_set[v][idx] = std::make_pair(true, curr_st);
                return curr_st;
            }
        }

        svector<lbool>         m_frontend_bvalues;
        unsigned_vector        m_frontend_unit_indices;
        bool_vector            m_frontend_used;

        inline static unsigned encode_unit_indices(unsigned idx, bool learned) {
            return 2 * idx + learned;
        }

        void frontend_propagate(literal l, unsigned idx, bool learned, bool used_in_search) {
            DTRACE(std::cout << "frontend propagate literal "; display(std::cout, l) << std::endl;);
            m_frontend_bvalues[l.var()] = l.sign() ? l_false : l_true;
            m_frontend_unit_indices[l.var()] = encode_unit_indices(idx, learned);
            m_frontend_used[l.var()] = used_in_search;
        }

        lbool frontend_value(literal l) const {
            if(m_frontend_bvalues[l.var()] == l_undef) {
                return l_undef;
            }
            return l.sign() ? ~m_frontend_bvalues[l.var()] : m_frontend_bvalues[l.var()];
        }

        lbool frontend_value(bool_var b) const {
            return m_frontend_bvalues[b];
        }
        
        void set_clause_literal_watcher(unsigned idx, bool & deleted) {
            deleted = false;
            clause const &curr_clause = *m_clauses[idx];
            SASSERT(curr_clause.size() > 0);
            if(curr_clause.size() == 1) {
                literal l = curr_clause[0];
                if(frontend_value(l) == l_false) {
                    frontend_conflict = true;
                    return;
                }
                frontend_propagate(l, idx, false, is_bool_literal(l));
                m_atom_unit_clauses[l.var()] = idx;
            } else {
                bool is_sat = false; unsigned id1 = null_var, id2 = null_var;
                for(int idx2 = 0; idx2 < curr_clause.size(); idx2++) {
                    literal l = curr_clause[idx2];
                    if(frontend_value(l) == l_true) {
                        is_sat = true;
                        break;
                    }
                    if(frontend_value(l) == l_false) {
                        continue;
                    }
                    if(id1 == null_var) {
                        id1 = idx2;
                    } else if(id2 == null_var) {
                        id2 = idx2;
                    }
                }
                if(is_sat) { // valid clause, delete it from front_end
                    del_clause(m_clauses[idx]);
                    deleted = true;
                    return;
                }
                if(id1 == null_var && id2 == null_var) { // conflict
                    frontend_conflict = true;
                }
                else if(id1 != null_var && id2 == null_var) { // unit clause
                    frontend_propagate(curr_clause[id1], idx, false, is_bool_literal(curr_clause[id1]));
                } else if(id1 != null_var && id2 != null_var) { // set watches
                    literal l1 = curr_clause[id1], l2 = curr_clause[id2];
                    int i1 = l1.sign() ? -l1.var() : l1.var();
                    int i2 = l2.sign() ? -l2.var() : l2.var();
                    SASSERT(i1 != 0 && i2 != 0);
                    clause_literal_watcher *new_watcher = new clause_literal_watcher(idx, i1, i2);
                    if(!l1.sign()) {
                        m_pos_literal_watching_clauses[l1.var()].push_back(new_watcher);
                    } else {
                        m_neg_literal_watching_clauses[l1.var()].push_back(new_watcher);
                    }
                    if(!l2.sign()) {
                        m_pos_literal_watching_clauses[l2.var()].push_back(new_watcher);
                    } else {
                        m_neg_literal_watching_clauses[l2.var()].push_back(new_watcher);
                    }
                    m_nlsat_clauses[idx]->m_atom_watcher = new_watcher;
                }
            }
        }

        void set_clause_var_watcher(unsigned idx) {
            nlsat_clause const *curr_clause = m_nlsat_clauses[idx];
            if(curr_clause->m_bool_vars.empty()) { // no bool var
                SASSERT(!curr_clause->m_vars.empty());
                auto it = curr_clause->m_vars.begin();
                if(curr_clause->m_vars.size() == 1) { // only one arith var
                    var v = *it;
                    m_arith_unit_clauses[v].push_back(idx);
                    if(m_clauses[idx]->size() > 1) {
                        m_arith_unit_clauses_more_lits[v].push_back(idx);
                    }
                    if(!update_clause_frontend_infeasible_set(idx, v)) { // conflict
                        frontend_conflict = true;
                        return;
                    } else {
                        if(m_clauses[idx]->size() == 1) {
                            frontend_propagate((*m_clauses[idx])[0], idx, false, true);
                        }
                    }
                } else { // more arith vars
                    var v1 = *it;
                    it++;
                    var v2 = *it;
                    clause_var_watcher *new_watcher = new clause_var_watcher(idx, arith2hybrid(v1), arith2hybrid(v2));
                    m_var_watching_clauses[arith2hybrid(v1)].push_back(new_watcher);
                    m_var_watching_clauses[arith2hybrid(v2)].push_back(new_watcher);
                    m_nlsat_clauses[idx]->m_var_watcher = new_watcher;
                }
            } else if(curr_clause->m_bool_vars.size() == 1) { // one bool var
                auto it = curr_clause->m_bool_vars.begin();
                bool_var b = *it;
                if(curr_clause->m_vars.empty()) { // unit bool var, propagate in unit propagation before
                    // do nothing
                } else { // one bool var and more arith vars
                    auto it2 = curr_clause->m_vars.begin();
                    var v = *it2;
                    clause_var_watcher *new_watcher = new clause_var_watcher(idx, b, arith2hybrid(v));
                    m_var_watching_clauses[b].push_back(new_watcher);
                    m_var_watching_clauses[arith2hybrid(v)].push_back(new_watcher);
                    m_nlsat_clauses[idx]->m_var_watcher = new_watcher;
                }
            } else { // more bool vars
                SASSERT(curr_clause->m_bool_vars.size() >= 2);
                auto it = curr_clause->m_bool_vars.begin();
                bool_var b1 = *it;
                it++;
                bool_var b2 = *it;
                clause_var_watcher *new_watcher = new clause_var_watcher(idx, b1, b2);
                m_var_watching_clauses[b1].push_back(new_watcher);
                m_var_watching_clauses[b2].push_back(new_watcher);
                m_nlsat_clauses[idx]->m_var_watcher = new_watcher;
            }
        }

        void init_reduce_options() {
            max_learnts = m_clauses.size() * OPTIONS::learnt_size_fatcor;
            if(max_learnts < OPTIONS::min_learnt_size) {
                max_learnts = OPTIONS::min_learnt_size;
            }
            m_reduce_threshold = OPTIONS::reduce_init_conf;
        }

        /**
          \brief fix a static order, used for debug
        */
        void fix_order() {
            // y z x
            // x y z
            var_vector perm;
            perm.resize(3, 0);
            perm[0] = 1;
            perm[1] = 2;
            perm[2] = 0;
            reorder(perm.size(), perm.data());
            display_vars(std::cout);
        }

        lbool check() {
            DTRACE(std::cout << "start check..." << std::endl;);
            // fix_order();
            register_nlsat_structures();
            DTRACE(std::cout << "register nlsat structures done" << std::endl;);
            if (!m_incremental && m_inline_vars) {
                if (!simplify()) 
                    return l_false;
            }
            if (frontend_conflict) return l_false;
            init_search();
            DTRACE(display_vars(std::cout););
            m_explain.set_full_dimensional(is_full_dimensional());
            if(OPTIONS::enable_reduce) init_reduce_options();
            return search_check();
        }

        void init_search() {
            m_hk = null_var;
            undo_until_empty();
            SASSERT(m_scope_lvl == 0);
            // TODO:
            if(m_scope_lvl != 0) {
                UNREACHABLE();
            }
            clear_assignment();
            m_scope_stage = 0;
            clear_nlsat_trails();
            // clear_infeasible_set_cache();
            build_var_heap();
            build_frontend_info();
            conflict_clause = nullptr;
            generate_during_process = true;
        }

        void build_var_heap() {
            m_var_heap.clear();
            m_var_heap.set_bounds(m_num_hybrid_vars);
            for(hybrid_var v = 0; v < m_num_hybrid_vars; v++){
                m_var_heap.insert(v);
            }
        }

        void build_frontend_info() {
            build_frontend_assignment();
            build_frontend_infeasible_set();
        }

        void build_frontend_assignment() {
            for(bool_var b = 0; b < m_atoms.size(); b++) {
                if(frontend_value(b) != l_undef && m_frontend_unit_indices[b] != null_var && m_frontend_used[b]) {
                    assign_literal(
                        literal(b, frontend_value(b) == l_false), 
                        mk_clause_jst(m_frontend_unit_indices[b] % 2 == 0 ? 
                                        m_clauses[m_frontend_unit_indices[b] / 2] : m_learned[m_frontend_unit_indices[b] / 2])
                    );
                }
            }
            DTRACE(std::cout << "build frontend assignment done" << std::endl;);
        }

        void build_frontend_infeasible_set() {
            for(var v = 0; v < num_arith_vars(); v++) {
                if(m_frontend_infeasible[v] != nullptr) {
                    save_set_updt_trail(v, m_infeasible[v]);
                    m_ism.inc_ref(m_frontend_infeasible[v]);
                    m_infeasible[v] = m_frontend_infeasible[v];
                }
            }
            DTRACE(std::cout << "build frontend infeasible done" << std::endl;);
        }

        lbool check(literal_vector& assumptions) {
            literal_vector result;
            unsigned sz = assumptions.size();
            literal const* ptr = assumptions.data();
            for (unsigned i = 0; i < sz; ++i) {
                mk_clause(1, ptr+i, (assumption)(ptr+i));
            }
            display_literal_assumption dla(*this, assumptions);
            scoped_display_assumptions _scoped_display(*this, dla);
            lbool r = check();
            if (r == l_false) {
                // collect used literals from m_lemma_assumptions
                vector<assumption, false> deps;
                get_core(deps);
                for (unsigned i = 0; i < deps.size(); ++i) {
                    literal const* lp = (literal const*)(deps[i]);
                    if (ptr <= lp && lp < ptr + sz) {
                        result.push_back(*lp);
                    } 
                }
            }
            collect(assumptions, m_clauses);
            collect(assumptions, m_learned);
            del_clauses(m_valids);
            if (m_check_lemmas) {
                for (clause* c : m_learned) {
                    check_lemma(c->size(), c->data(), false, nullptr);
                }
            }

#if 0
            for (clause* c : m_learned) {
                IF_VERBOSE(0, display(verbose_stream() << "KEEP: ", c->size(), c->c_ptr()) << "\n");
            }
#endif
            assumptions.reset();
            assumptions.append(result);
            return r;
        }

        void get_core(vector<assumption, false>& deps) {
            m_asm.linearize(m_lemma_assumptions.get(), deps);
        }

        void collect(literal_vector const& assumptions, clause_vector& clauses) {
            unsigned j  = 0;
            for (clause * c : clauses) {
                if (collect(assumptions, *c)) {
                    del_clause(c);
                }
                else {
                    clauses[j++] = c;
                }
            }
            clauses.shrink(j);
        }

        bool collect(literal_vector const& assumptions, clause const& c) {
            unsigned sz = assumptions.size();
            literal const* ptr = assumptions.data();            
            _assumption_set asms = static_cast<_assumption_set>(c.assumptions());
            if (asms == nullptr) {
                return false;
            }
            vector<assumption, false> deps;
            m_asm.linearize(asms, deps);
            for (auto dep : deps) {
                if (ptr <= dep && dep < ptr + sz) {
                    return true;
                }
            }
            return false;
        }

        // -----------------------
        //
        // Conflict Resolution
        //
        // -----------------------
        svector<char>          m_marks;        // bool_var -> bool  temp mark used during conflict resolution
        unsigned               m_num_marks;
        scoped_literal_vector  m_lemma;
        scoped_literal_vector  m_lazy_clause;
        assumption_set_ref     m_lemma_assumptions; // assumption tracking

        // Conflict resolution invariant: a marked literal is in m_lemma or on the trail stack.

        bool check_marks() {
            for (unsigned m : m_marks) {
                (void)m;
                SASSERT(m == 0);
            }
            return true;
        }
        
        unsigned scope_lvl() const { return m_scope_lvl; }
        
        bool is_marked(bool_var b) const { return m_marks.get(b, 0) == 1; }

        void mark(bool_var b) { m_marks.setx(b, 1, 0); }
        
        void reset_mark(bool_var b) { m_marks[b] = 0; }

        void reset_marks() {
            for (auto const& l : m_lemma) {
                reset_mark(l.var());
            }
        }

        void insert_conflict_from_atom(bool_var b){
            for(var v: m_nlsat_atoms[b]->m_vars){
                m_conflict_arith.insert_if_not_there(v);
            }
            if(m_atoms[b] == nullptr){
                m_conflict_bool.insert_if_not_there(m_pure_bool_convert[b]);
            }
        }

        void insert_conflict_from_literals(unsigned sz, literal const * ls){
            for(unsigned i = 0; i < sz; i++){
                literal l = ls[i];
                insert_conflict_from_atom(l.var());
            }
        }

        bool max_arith_level(bool_var b) const {
            return m_atoms[b] != nullptr ?
                m_arith_level[b] == arith_level(hybrid2arith(m_hk), 
                            m_var_max_level[hybrid2arith(m_hk)]) : m_levels[b] == m_scope_lvl;
        }

        void process_antecedent(literal antecedent) {
            DTRACE(std::cout << "process antecedent for literal: "; display(std::cout, antecedent) << std::endl;);
            checkpoint();
            bool_var b  = antecedent.var();
            insert_conflict_from_atom(b);
            if (assigned_value(antecedent) == l_undef) {
                checkpoint();
                // antecedent must be false in the current arith interpretation
                SASSERT(value(antecedent) == l_false || m_rlimit.is_canceled());
                if (!is_marked(b)) {
                    SASSERT(is_arith_atom(b) && all_assigned(a)); // must be in a previous stage
                    mark(b);
                    m_lemma.push_back(antecedent);
                    DTRACE(std::cout << "case 1 antecedent, push back lemma: "; display(std::cout, antecedent) << std::endl;);
                }
                return;
            }
            if (!is_marked(b)) {
                mark(b);
                arith_level curr = m_arith_level[b];
                // if(b_lvl == scope_lvl() && same_stage_atom(b, m_scope_stage)){
                if(same_stage_atom(b, m_scope_stage) && max_arith_level(b)) {
                    m_num_marks++;
                    DTRACE(std::cout << "same stage and same level, increase mark " << m_num_marks << std::endl;);
                }
                else {
                    m_lemma.push_back(antecedent);
                    DTRACE(std::cout << "case 2 antecedent, push back lemma: "; display(std::cout, antecedent) << std::endl;);
                }
            }
        }

        void resolve_clause(bool_var b, unsigned sz, literal const * c) {
            DTRACE(std::cout << "resolve clause" << std::endl;);
            insert_conflict_from_literals(sz, c);
            for (unsigned i = 0; i < sz; i++) {
                if (c[i].var() != b)
                    process_antecedent(c[i]);
            }
            DTRACE(std::cout << "resolve clause done" << std::endl;);
        }

        // remember here we delete const clause
        void resolve_clause(bool_var b, clause & c) {
            resolve_clause(b, c.size(), c.data());
            if(c.is_learned()){
                clause_bump_act(c);
            }
            m_lemma_assumptions = m_asm.mk_join(static_cast<_assumption_set>(c.assumptions()), m_lemma_assumptions);
        }

        void insert_conflict_vars_from_literals(unsigned sz, literal const *ls) {
            for(unsigned i = 0; i < sz; i++){
                literal l = ls[i];
                insert_conflict_vars_from_atom(l.var());
            }
        }

        void insert_conflict_vars_from_atom(bool_var b) {
            if(m_atoms[b] != nullptr) { // arith atom
                for(var v: m_nlsat_atoms[b]->m_vars){
                    m_conflict_arith.insert_if_not_there(v);
                }
            } else {
                m_conflict_bool.insert_if_not_there(m_pure_bool_convert[b]);
            }
        }

        void resolve_lazy_justification(bool_var b, lazy_justification const & jst) {
            unsigned sz = jst.num_lits();
            m_lazy_clause.reset();
            DTRACE(std::cout << "enter explain" << std::endl;);
            DTRACE("enter explain lits: ";
                display(std::cout, jst.num_lits(), jst.lits()) << std::endl;
            );
            m_explain(jst.num_lits(), jst.lits(), m_lazy_clause);
            for (unsigned i = 0; i < sz; i++)
                m_lazy_clause.push_back(~jst.lit(i));
            DTRACE(std::cout << "new valid clause in explain:\n";
            display(std::cout, m_lazy_clause.size(), m_lazy_clause.data()) << "\n";);
            insert_conflict_vars_from_literals(m_lazy_clause.size(), m_lazy_clause.data());

            if (m_check_lemmas) {
                m_valids.push_back(mk_clause_core(m_lazy_clause.size(), m_lazy_clause.data(), false, nullptr));
            }
            
            DEBUG_CODE({
                unsigned sz = m_lazy_clause.size();
                for (unsigned i = 0; i < sz; i++) {
                    literal l = m_lazy_clause[i];
                    if (l.var() != b) {
                        SASSERT(value(l) == l_false || m_rlimit.is_canceled());
                    }
                    else {
                        SASSERT(value(l) == l_true || m_rlimit.is_canceled());
                        SASSERT(!l.sign() || m_bvalues[b] == l_false);
                        SASSERT(l.sign()  || m_bvalues[b] == l_true);
                    }
                }
            });
            checkpoint();
            resolve_clause(b, m_lazy_clause.size(), m_lazy_clause.data());
            for (unsigned i = 0; i < jst.num_clauses(); ++i) {
                clause const& c = jst.clause(i);
                m_lemma_assumptions = m_asm.mk_join(static_cast<_assumption_set>(c.assumptions()), m_lemma_assumptions);
            }
            DTRACE(std::cout << "resolve lazy done" << std::endl;);
        }

        /**
          \brief Stage Manager
        */
       unsigned find_hybrid_var_stage(hybrid_var x) const {
            if(x == null_var) {
                return null_var;
            }
            SASSERT(x < m_num_hybrid_vars);
            return m_hybrid_find_stage[x];
       }

        bool same_stage_literal(literal l, unsigned stg) const {
            return max_stage_literal(l) == stg;
        }

        unsigned max_stage_literals(unsigned sz, literal const *ls) const {
            unsigned res = 0;
            for(unsigned i = 0; i < sz; i++) {
                literal l = ls[i];
                unsigned curr_stg = max_stage_literal(l);
                if(res == 0 || curr_stg > res) {
                    res = curr_stg;
                }
            }
            return res;
        }

        unsigned max_stage_literal(literal l) const {
            return max_stage_atom(l.var());
        }

        bool same_stage_atom(bool_var b, unsigned stg) const {
            return max_stage_atom(b) == stg;
        }

        var max_stage_var(atom const * a) const {
            auto const * curr = m_nlsat_atoms[a->bvar()];
            if(curr->m_vars.empty()){
                return null_var;
            }
            var res = *(curr->m_vars.begin());
            unsigned max_stage = find_hybrid_var_stage(arith2hybrid(res));
            for(var cur: curr->m_vars){
                var curr_stage = find_hybrid_var_stage(arith2hybrid(cur));
                if(curr_stage > max_stage){
                    max_stage = curr_stage;
                    res = cur;
                }
            }
            return res;
        }

        unsigned max_stage_atom(bool_var b) const {
            if(m_atoms[b] == nullptr) {
                return find_hybrid_var_stage(m_pure_bool_convert[b]);
            } else {
                nlsat_atom const *a = m_nlsat_atoms[b];
                unsigned res = 0;
                for(var v: a->m_vars) {
                    unsigned curr_stage = find_hybrid_var_stage(arith2hybrid(v));
                    if(res == 0 || curr_stage > res) {
                        res = curr_stage;
                    }
                    if(res == null_var) {
                        return null_var;
                    }
                }
                return res;
            }
        }

        unsigned max_stage_poly(poly const *p) const {
            var_vector curr;
            m_pm.vars(p, curr);
            unsigned x = 0;
            for(var v: curr) {
                unsigned curr_stg = find_hybrid_var_stage(arith2hybrid(v));
                if(x == 0 || curr_stg > x) {
                    x = curr_stg;
                }
                if(x == null_var) {
                    return null_var;
                }
            }
            return x;
        }

        var max_stage_var_poly(poly const * p) const {
            var_vector curr;
            m_pm.vars(p, curr);
            var res_x = 0, max_stage = 0;
            for(var v: curr){
                var curr_stage = find_hybrid_var_stage(arith2hybrid(v));
                if(max_stage == 0 || curr_stage > max_stage){
                    max_stage = curr_stage;
                    res_x = v;
                }
            }
            return res_x;
        }

        void get_vars_ps(polynomial_ref_vector const & ps, var_table & vec) const {
            vec.reset();
            for(unsigned i = 0; i < ps.size(); i++){
                var_vector curr;
                poly * p = ps.get(i);
                m_pm.vars(p, curr);
                for(var v: curr){
                    vec.insert_if_not_there(v);
                }
            }
        }

        var max_stage_or_unassigned_ps(polynomial_ref_vector const & ps) const {
            var_table curr_vars;
            get_vars_ps(ps, curr_vars);
            var max_stage = 0, res_x = null_var;
            for(var v: curr_vars){
                if(!m_assignment.is_assigned(v)){
                    return v;
                }
                var curr = find_hybrid_var_stage(arith2hybrid(v));
                if(max_stage == 0 || curr > max_stage){
                    max_stage = curr;
                    res_x = v;
                }
            }
            return res_x;
        }

        void get_vars_literals(unsigned num, literal const * ls, var_table & vec) const {
            vec.reset();
            for(unsigned i = 0; i < num; i++){
                literal l = ls[i];
                for(var v: m_nlsat_atoms[l.var()]->m_vars){
                    vec.insert_if_not_there(v);
                }
            }
        }

        var max_stage_or_unassigned_literals(unsigned num, literal const * ls) const {
            var_table curr_vars;
            get_vars_literals(num, ls, curr_vars);
            var max_stage = 0, res_x = null_var;
            for(var v: curr_vars){
                if(!m_assignment.is_assigned(v)){
                    return v;
                }
                var curr_stage = find_hybrid_var_stage(arith2hybrid(v));
                if(max_stage == 0 || curr_stage > max_stage){
                    max_stage = curr_stage;
                    res_x = v;
                }
            }
            return res_x;
        }

        var max_stage_or_unassigned_atom(atom const * a) const {
            var max_stage = 0, res_x = null_var;
            for(var v: m_nlsat_atoms[a->bvar()]->m_vars){
                if(!m_assignment.is_assigned(v)){
                    return v;
                }
                var curr_stage = find_hybrid_var_stage(arith2hybrid(v));
                if(max_stage == 0 || curr_stage > max_stage){
                    max_stage = curr_stage;
                    res_x = v;
                }
            }
            return res_x;
        }

        void get_bool_vars_literals(unsigned num, literal const * ls, bool_var_table & vec) const {
            vec.reset();
            for(unsigned i = 0; i < num; i++){
                literal l = ls[i];
                if(m_atoms[l.var()] == nullptr){
                    vec.insert_if_not_there(m_pure_bool_convert[l.var()]);
                }
            }
        }

        /**
          \brief Given literals' vars are all unassigned
        */
        bool all_unassigned(unsigned sz, literal const *ls) const {
            var_table curr_vars;
            bool_var_table curr_bools;
            get_vars_literals(sz, ls, curr_vars);
            get_bool_vars_literals(sz, ls, curr_bools);
            for(var v: curr_vars) {
                if(m_assignment.is_assigned(v)) {
                    return false;
                }
            }
            for(bool_var b: curr_bools) {
                if(m_bvalues[m_pure_bool_vars[b]] != l_undef) {
                    return false;
                }
            }
            return true;
        }

        /**
          \brief Find max assigned var, ignore unassigned var
        */
        hybrid_var max_assigned_var(unsigned sz, literal const * ls, bool & is_bool, unsigned & max_stage) const {
            SASSERT(!all_unassigned(sz, ls));
            hybrid_var res = null_var;
            var_table curr_vars;
            bool_var_table curr_bools;
            get_vars_literals(sz, ls, curr_vars);
            get_bool_vars_literals(sz, ls, curr_bools);
            unsigned max_index = 0;
            for(var v: curr_vars){
                var index = find_assigned_index(arith2hybrid(v));
                if(index == null_var){
                    continue;
                }
                else {
                    if(index >= max_index){
                        max_index = index;
                        res = v;
                        is_bool = false;
                    }
                }
            }
            for(bool_var b: curr_bools){
                var index = find_assigned_index(b);
                if(index == null_var){
                    UNREACHABLE();
                }
                else {
                    if(index >= max_index){
                        max_index = index;
                        res = b;
                        is_bool = true;
                    }
                }
            }
            max_stage = find_hybrid_var_stage(is_bool ? res : arith2hybrid(res));
            return res;
        }

        unsigned find_assigned_index(hybrid_var x) const {
            return m_hybrid_assigned_indices[x];
        }
        
        /**
           \brief Return true if all literals in ls are from previous stages.
        */
        bool only_literals_from_previous_stages(unsigned num, literal const * ls) {
            for (unsigned i = 0; i < num; i++) {
                if(same_stage_literal(ls[i], m_scope_stage)){
                    return false;
                }
            }
            return true;
        }

        /**
           \brief Return the maximum scope level in ls. 
           
           \pre This method assumes value(ls[i]) is l_false for i in [0, num)
        */
        unsigned max_scope_lvl(unsigned num, literal const * ls) {
            unsigned max = 0;
            for (unsigned i = 0; i < num; i++) {
                literal l = ls[i];
                bool_var b = l.var();
                SASSERT(value(ls[i]) == l_false);
                if (assigned_value(l) == l_false) {
                    unsigned lvl = m_levels[b];
                    if (lvl > max)
                        max = lvl;
                }
                else {
                    // l must be a literal from a previous stage that is false in the current interpretation
                    SASSERT(assigned_value(l) == l_undef);
                    SASSERT(m_xk       != null_var);
                }
            }
            return max;
        }

        /**
           \brief Remove literals of the given lvl (that are in the current stage) from lemma.

           \pre This method assumes value(ls[i]) is l_false for i in [0, num)
        */
        void remove_literals_from_lvl(scoped_literal_vector & lemma, unsigned lvl) {
            unsigned sz = lemma.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; i++) {
                literal l = lemma[i];
                bool_var b = l.var();
                SASSERT(is_marked(b));
                SASSERT(value(lemma[i]) == l_false);
                if (assigned_value(l) == l_false && same_stage_atom(b, m_scope_stage) && m_levels[b] == lvl) {
                    m_num_marks++;
                    continue;
                }
                lemma.set(j, l);
                j++;
            }
            lemma.shrink(j);
        }

        /**
           \brief Return true if it is a Boolean lemma.
        */
        bool is_bool_lemma(unsigned sz, literal const * ls) const {
            for (unsigned i = 0; i < sz; i++) {
                if (m_atoms[ls[i].var()] != nullptr)
                    return false;
            }
            return true;
        }


        /** 
            Return the maximal decision level in lemma for literals in the first sz-1 positions that 
            are at the same stage. If all these literals are from previous stages,
            we just backtrack the current level.
        */
        unsigned find_new_level_arith_lemma(unsigned sz, literal const * lemma) {
            SASSERT(!is_bool_lemma(sz, lemma));
            unsigned new_lvl = 0;
            bool found_lvl   = false;
            for (unsigned i = 0; i < sz - 1; i++) {
                literal l = lemma[i];
                if(same_stage_literal(l, m_scope_stage)){
                    bool_var b = l.var();
                    if (!found_lvl) {
                        found_lvl = true;
                        new_lvl   = m_levels[b];
                    }
                    else {
                        if (m_levels[b] > new_lvl)
                            new_lvl = m_levels[b];
                    }
                }
            }
            SASSERT(!found_lvl || new_lvl < scope_lvl());
            if (!found_lvl) {
                new_lvl = scope_lvl() - 1;
            }
            return new_lvl;
        }

        struct scoped_reset_marks {
            imp& i;
            scoped_reset_marks(imp& i):i(i) {}
            ~scoped_reset_marks() { if (i.m_num_marks > 0) { i.m_num_marks = 0; for (char& m : i.m_marks) m = 0; } }
        };

        void reset_conflict_vars() {
            m_conflict_arith.reset();
            m_conflict_bool.reset();
        }

        void hybrid_decay_act(){
            arith_decay_act();
            bool_var_decay_act();
        }

        void arith_decay_act(){
            arith_var_bump *= (1.0 / OPTIONS::arith_var_decay);
        }

        void bool_var_decay_act(){
            bool_var_bump *= (1.0 / OPTIONS::bool_var_decay);
        }

        void clause_decay_act(){
            clause_bump *= (1 / OPTIONS::clause_decay);
        }

        void update_learnt_management(){
            if(--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= OPTIONS::learnt_size_inc;
                learntsize_adjust_cnt = (int) learntsize_adjust_confl;
                max_learnts *= OPTIONS::learnt_size_inc;
            }
        }

        bool contains(scoped_literal_vector const &vec, literal l) const {
            for(unsigned i = 0; i < vec.size(); i++) {
                if(vec[i] == l) {
                    return true;
                }
            }
            return false;
        }

        /**
           \brief Return true if the conflict was solved.
        */
       // remember here we delete const clause
        bool resolve(clause & conflict) {
            m_lemma_assumptions = nullptr;
            SASSERT(check_marks());
            reset_conflict_vars();
            m_conflicts++;
            m_restart_conflicts++;
            m_reduce_conflicts++;
            m_num_marks = 0;
            m_lemma.reset();
            m_lemma_assumptions = nullptr;
            scoped_reset_marks _sr(*this);
            DTRACE(std::cout << "conflict clause: "; 
                display(std::cout, conflict) << std::endl;
                std::cout << "m_hk: " << m_hk <<" ";
                if(hybrid_is_arith(m_hk)) {
                    std::cout << "arith "; m_display_var(std::cout, hybrid2arith(m_hk)) << std::endl;
                }
                display_assignment(std::cout);
                display_hybrid_trail(std::cout);
            );
            resolve_clause(null_bool_var, *conflict_clause);
            unsigned top = m_trail.size();
            bool found_decision;
            while (true) {
                found_decision = false;
                while (m_num_marks > 0) {
                    checkpoint();
                    SASSERT(top > 0);
                    trail & t = m_trail[top-1];
                    SASSERT(t.m_kind != trail::NEW_STAGE); // we only mark literals that are in the same stage
                    if (t.m_kind == trail::BVAR_ASSIGNMENT) {
                        bool_var b = t.m_x;
                        DTRACE(std::cout << "show trail bool: "; display_atom(std::cout, b) << std::endl;);
                        insert_conflict_vars_from_atom(b);
                        if (is_marked(b)) {
                            m_num_marks--;
                            reset_mark(b);
                            justification jst = m_justifications[b];
                            switch (jst.get_kind()) {
                            case justification::CLAUSE:
                                DTRACE(std::cout << "unit propagate case, resolve clause" << std::endl;);
                                resolve_clause(b, *(jst.get_clause()));
                                DTRACE(std::cout << "resolve clause done" << std::endl;);
                                break;
                            case justification::LAZY:
                                DTRACE(std::cout << "real propagate case, resolve lazy" << std::endl;);
                                resolve_lazy_justification(b, *(jst.get_lazy()));
                                DTRACE(std::cout << "resolve lazy done" << std::endl;);
                                break;
                            case justification::DECISION:
                                SASSERT(m_num_marks == 0);
                                DTRACE(std::cout << "decision case, push literal into lemma" << std::endl;);
                                found_decision = true;
                                if (!contains(m_lemma, literal(b, m_bvalues[b] == l_true))) {
                                    m_lemma.push_back(literal(b, m_bvalues[b] == l_true));
                                }
                                DTRACE(std::cout << "push literal done" << std::endl;);
                                break;
                            default:
                                UNREACHABLE();
                                break;
                            }
                        }
                    }
                    top--;
                }
                DTRACE(std::cout << "current lemma: ";
                    display(std::cout, m_lemma.size(), m_lemma.data()) << std::endl;
                );
                DTRACE(std::cout << "bump hybrid vars" << std::endl;);
                bump_conflict_hybrid_vars();
                DTRACE(std::cout << "bump hybrid vars done" << std::endl;);
                // m_lemma is an implicating clause after backtracking current scope level.
                if (found_decision){
                    DTRACE(std::cout << "case 1, found decision" << std::endl;);
                    break;
                }
                // If lemma only contains literals from previous stages, then we can stop.
                // We make progress by returning to a previous stage with additional information (new lemma)
                // that forces us to select a new partial interpretation
                if (only_literals_from_previous_stages(m_lemma.size(), m_lemma.data())){
                    DTRACE(std::cout << "case 2, all previous stages" << std::endl;);
                    break;
                }
                // Conflict does not depend on the current decision, and it is still in the current stage.
                // We should find
                //    - the maximal scope level in the lemma
                //    - remove literal assigned in the scope level from m_lemma
                //    - backtrack to this level
                //    - and continue conflict resolution from there
                //    - we must bump m_num_marks for literals removed from m_lemma
                DTRACE(std::cout << "case 3, Conflict does not depend on the current decision, and it is still in the current stage" << std::endl;);
                unsigned max_lvl = max_scope_lvl(m_lemma.size(), m_lemma.data());
                SASSERT(max_lvl < scope_lvl());
                remove_literals_from_lvl(m_lemma, max_lvl);
                undo_until_level(max_lvl);
                top = m_trail.size();
                SASSERT(scope_lvl() == max_lvl);
            }
            if (m_lemma.empty()) {
                return false; // problem is unsat, empty clause was generated
            }
            reset_marks(); // remove marks from the literals in m_lemmas.
            if (false && m_check_lemmas) {
                check_lemma(m_lemma.size(), m_lemma.data(), false, m_lemma_assumptions.get());
            }
    
            // There are two possibilities:
            // 1) m_lemma contains only literals from previous stages, and they
            //    are false in the current interpretation. We make progress 
            //    by returning to a previous stage with additional information (new clause)
            //    that forces us to select a new partial interpretation
            //    >>> Return to some previous stage (we may also backjump many decisions and stages).
            //    
            // 2) m_lemma contains at most one literal from the current level (the last literal).
            //    Moreover, this literal was a decision, but the new lemma forces it to 
            //    be assigned to a different value.
            //    >>> In this case, we remain in the same stage but, we add a new asserted literal
            //        in a previous scope level. We may backjump many decisions.
            //
            unsigned sz = m_lemma.size();
            clause * new_cls = nullptr;
            conflict_clause = nullptr; // clear conflict this time
            DTRACE(std::cout << "show lemma:\n";
                display(std::cout, sz, m_lemma.data()) << std::endl;
            );
            if (!found_decision) {
                // special case:
                // all vars in m_lemma is unassigned and we found no decision
                if(all_unassigned(sz, m_lemma.data())) {
                    DTRACE(std::cout << "found no decision, and current lemma is all unassigned";
                        std::cout << "we return to unsat" << std::endl;
                    );
                    return false;
                }

                // Case 1)
                // We just have to find the maximal variable in m_lemma, and return to that stage
                // previous: Remark: the lemma may contain only boolean literals, in this case new_max_var == null_var;
                // current: for boolean literals, new_max_var is the max_stage of boolean literals, since we may peek bool var after arith var
                bool is_bool;
                unsigned max_stage;
                hybrid_var new_max_hybrid_var = max_assigned_var(sz, m_lemma.data(), is_bool, max_stage);
                // case 1.1
                // max var is bool var, we backtrack to max stage of this bool var
                // note that this bool var should be assigned after undoing stages
                if(is_bool){
                    undo_until_stage(max_stage);
                }
                // case 1.2
                // max var is arith var, we backtrack until the max arith var is unassigned
                else {
                    undo_until_unassigned(new_max_hybrid_var, false);
                }

                // generate new clause based on lemma's contained literals
                new_cls = mk_clause(sz, m_lemma.data(), true, m_lemma_assumptions.get());
            }
            else { // found decision
                SASSERT(scope_lvl() >= 1);
                // Case 2)
                if (is_bool_lemma(m_lemma.size(), m_lemma.data())) {
                    // boolean lemma, we just backtrack until the last literal is unassigned.
                    bool_var max_bool_var = m_lemma[m_lemma.size() - 1].var();
                    undo_until_unassigned(m_pure_bool_convert[max_bool_var], true);
                }
                else {
                    // We must find the maximal decision level in literals in the first sz-1 positions that 
                    // are at the same stage. If all these literals are from previous stages,
                    // we just backtrack the current level.
                    undo_until_level(find_new_level_arith_lemma(m_lemma.size(), m_lemma.data()));
                }
                new_cls = mk_clause(sz, m_lemma.data(), true, m_lemma_assumptions.get());
            }
            DTRACE(std::cout << "new lemma: "; display(std::cout, sz, m_lemma.data()) << std::endl;);
            hybrid_decay_act();
            clause_decay_act();
            if(OPTIONS::enable_reduce) {
                update_learnt_management();
            }
            NLSAT_VERBOSE(display(verbose_stream(), *new_cls) << "\n";);
            DTRACE(std::cout << "resolve done ..." << std::endl;);
            return true; // clause learning finished, return to solving procedure and propagate
        }

        // bool index: pure bool index
        bool not_assigned_hybrid_var(hybrid_var v, bool is_bool){
            return is_bool ? m_bvalues[m_pure_bool_vars[v]] == l_undef : m_assignment.is_assigned(v);
        }

        bool lemma_is_clause(clause const& cls) const {
            bool same = (m_lemma.size() == cls.size());
            for (unsigned i = 0; same && i < m_lemma.size(); ++i) {
                same = m_lemma[i] == cls[i];
            }
            return same;
        }

        bool check_invariant() const {
            // SASSERT(check_watches());
            SASSERT(check_bwatches());
            return true;
        }
        
        // -----------------------
        //
        // Statistics
        //
        // -----------------------

        void collect_statistics(statistics & st) {
            st.update("nlsat conflicts", m_conflicts);
            st.update("nlsat real propagate", m_real_propagate);
            st.update("nlsat decisions", m_decisions);
            st.update("nlsat stages", m_stages);
            st.update("nlsat irrational assignments", m_irrational_assignments);
            st.update("nlsat bool vars", num_bool_vars());
            st.update("nlsat arith vars", num_arith_vars());
            st.update("nlsat total vars", m_num_hybrid_vars);
            st.update("nlsat unit propagate", m_unit_propagate);
            st.update("nlsat restarts", m_restarts);
            st.update("nlsat learned added", m_learned_added);
            st.update("nlsat learned deleted", m_learned_deleted);
        }

        void reset_overall_statistics() {
            m_conflicts              = 0;
            m_unit_propagate         = 0;
            m_real_propagate         = 0;
            m_decisions              = 0;
            m_stages                 = 0;
            m_irrational_assignments = 0;
            m_learned_added          = 0;
        }

        void reset_restart_statistics() {
            m_restarts               = 0;
            m_restart_conflicts      = 0;
        }

        void reset_reduce_statistics() {
            m_reduces                = 0;
            m_reduce_conflicts       = 0;
            m_learned_deleted        = 0;
        }

        void reset_statistics() {
            reset_overall_statistics();
            reset_restart_statistics();
            reset_reduce_statistics();
        }

        bool can_reorder() const {
            for (clause* c : m_learned) {
                if (has_root_atom(*c)) return false;
            }
            for (clause* c : m_clauses) {
                if (has_root_atom(*c)) return false;
            }
            return m_patch_var.empty();
        }

        /**
           \brief Reorder variables using the giving permutation.
           p maps internal variables to their new positions
        */
        void reorder(unsigned sz, var const * p) {
            remove_learned_roots();
            SASSERT(can_reorder());
            SASSERT(num_arith_vars() == sz);
            assignment new_assignment(m_am);
            for (var x = 0; x < num_arith_vars(); x++) {
                if (m_assignment.is_assigned(x)) 
                    new_assignment.set(p[x], m_assignment.value(x));
            }
            var_vector new_inv_perm;
            new_inv_perm.resize(sz);
            undo_until_stage(null_var);
            m_cache.reset();               
            DEBUG_CODE({
                for (var x = 0; x < num_arith_vars(); x++) {
                    SASSERT(m_watches[x].empty());
                }
            });
            // update m_perm mapping
            for (unsigned ext_x = 0; ext_x < sz; ext_x++) {
                new_inv_perm[ext_x] = p[m_inv_perm[ext_x]];
                m_perm.set(new_inv_perm[ext_x], ext_x);
            }
            bool_vector is_int;
            is_int.swap(m_is_int);
            for (var x = 0; x < sz; x++) {
                m_is_int.setx(p[x], is_int[x], false);
                SASSERT(m_infeasible[x] == 0);
            }
            m_inv_perm.swap(new_inv_perm);
            DEBUG_CODE({
                for (var x = 0; x < num_arith_vars(); x++) {
                    SASSERT(x == m_inv_perm[m_perm[x]]);
                    SASSERT(m_watches[x].empty());
                }
            });
            m_pm.rename(sz, p);
            reinit_cache();
            m_assignment.swap(new_assignment);
        }

        
        /**
           \brief Restore variable order.
        */
        void restore_order() {
            // m_perm: internal -> external
            // m_inv_perm: external -> internal            
            var_vector p;
            p.append(m_perm);
            reorder(p.size(), p.data());
            DEBUG_CODE({
                for (var x = 0; x < num_arith_vars(); x++) {
                    SASSERT(m_perm[x] == x);
                    SASSERT(m_inv_perm[x] == x);
                }
            });
        }

        /**
           \brief After variable reordering some lemmas containing root atoms may be ill-formed.
        */
        void remove_learned_roots() {
            unsigned j  = 0;
            // wzh dynamic
            // for (clause* c : m_learned) {
            for(unsigned i = 0; i < m_learned.size(); i++){
                clause * c = m_learned[i];
                if (has_root_atom(*c)) {
                    del_clause(c);
                }
                else {
                    // wzh dynamic
                    m_learned[j] = c;
                    j++;
                    // hzw dynamic
                }
            }
            m_learned.shrink(j);
        }

        /** 
            \brief Return true if the clause contains an ill formed root atom
        */
        bool has_root_atom(clause const & c) const {
            for (literal lit : c) {
                bool_var b = lit.var();
                atom * a = m_atoms[b];
                if (a && a->is_root_atom()) 
                    return true;
            }
            return false;
        }

        /**
           \brief reinsert all polynomials in the unique cache
        */
        void reinit_cache() {
            reinit_cache(m_clauses);
            reinit_cache(m_learned);
            for (atom* a : m_atoms) 
                reinit_cache(a);            
        }
        void reinit_cache(clause_vector const & cs) {
            for (clause* c : cs) 
                reinit_cache(*c);
        }
        void reinit_cache(clause const & c) {
            for (literal l : c) 
                reinit_cache(l);
        }
        void reinit_cache(literal l) {
            bool_var b = l.var();
            reinit_cache(m_atoms[b]);
        }
        void reinit_cache(atom* a) {
            if (a == nullptr) {

            }
            else if (a->is_ineq_atom()) {
                var max = 0;
                unsigned sz = to_ineq_atom(a)->size();
                for (unsigned i = 0; i < sz; i++) {
                    poly * p = to_ineq_atom(a)->p(i);
                    VERIFY(m_cache.mk_unique(p) == p);
                    // var x = m_pm.max_var(p);
                    // if (x > max)
                        // max = x;
                }
                // a->m_max_var = max;
            }
            else {
                poly * p = to_root_atom(a)->p();
                VERIFY(m_cache.mk_unique(p) == p);
                // a->m_max_var = m_pm.max_var(p);
            }
        }

        unsigned max_degree_of_stage_var(atom const * a) {
            var x = max_stage_var(a);
            if (a->is_ineq_atom()) {
                unsigned max = 0;
                unsigned sz  = to_ineq_atom(a)->size();
                for (unsigned i = 0; i < sz; i++) {
                    unsigned d = m_pm.degree(to_ineq_atom(a)->p(i), x);
                    if (d > max)
                        max = d;
                }
                return max;
            }
            else {
                return m_pm.degree(to_root_atom(a)->p(), x);
            }
        }

        // -----------------------
        //
        // Full dimensional 
        // 
        // A problem is in the full dimensional fragment if it does
        // not contain equalities or non-strict inequalities.
        //
        // -----------------------
        
        bool is_full_dimensional(literal l) const {
            atom * a = m_atoms[l.var()];
            if (a == nullptr)
                return true;
            switch (a->get_kind()) {
            case atom::EQ:      return l.sign();
            case atom::LT:      return !l.sign();
            case atom::GT:      return !l.sign();
            case atom::ROOT_EQ: return l.sign();
            case atom::ROOT_LT: return !l.sign();
            case atom::ROOT_GT: return !l.sign();
            case atom::ROOT_LE: return l.sign();
            case atom::ROOT_GE: return l.sign();
            default:
                UNREACHABLE();
                return false;
            }
        }

        bool is_full_dimensional(clause const & c) const {
            for (literal l : c) {
                if (!is_full_dimensional(l))
                    return false;
            }
            return true;
        }

        bool is_full_dimensional(clause_vector const & cs) const {
            for (clause* c : cs) {
                if (!is_full_dimensional(*c)) 
                    return false;
            }
            return true;
        }

        bool is_full_dimensional() const {
            return is_full_dimensional(m_clauses);
        }


        // -----------------------
        //
        // Simplification
        //
        // -----------------------

        // solve simple equalities
        // TBD WU-Reit decomposition?

        /**
           \brief isolate variables in unit equalities.
           Assume a clause is c == v*p + q
           and the context implies p > 0
           
           replace v by -q/p
           remove clause c, 
           The for other occurrences of v, 
              replace v*r + v*v*r' > 0 by 
              by p*p*v*r + p*p*v*v*r' > 0
              by p*q*r + q*q*r' > 0        

           The method ignores lemmas and assumes constraints don't use roots.
        */

        bool simplify() {
            polynomial_ref p(m_pm), q(m_pm);
            var v;
            init_var_signs();
            SASSERT(m_learned.empty());
            bool change = true;
            while (change) {
                change = false;
                for (clause* c : m_clauses) {
                    if (solve_var(*c, v, p, q)) {
                        q = -q;
                        m_patch_var.push_back(v);
                        m_patch_num.push_back(q);
                        m_patch_denom.push_back(p);
                        del_clause(c, m_clauses);
                        if (!substitute_var(v, p, q))
                            return false;
                        change = true;
                        break;
                    }
                }
            }
            return true;
        }

        void fix_patch() {
            for (unsigned i = m_patch_var.size(); i-- > 0; ) {
                var v = m_patch_var[i];
                poly* q = m_patch_num.get(i);
                poly* p = m_patch_denom.get(i);
                scoped_anum pv(m_am), qv(m_am), val(m_am);
                m_pm.eval(p, m_assignment, pv);
                m_pm.eval(q, m_assignment, qv);
                SASSERT(!m_am.is_zero(pv));
                val = qv / pv;
                m_assignment.set_core(v, val);
            }
        }

        bool substitute_var(var x, poly* p, poly* q) {
            bool is_sat = true;
            polynomial_ref pr(m_pm);
            polynomial_ref_vector ps(m_pm);

            u_map<literal> b2l;
            scoped_literal_vector lits(m_solver);
            bool_vector even;
            unsigned num_atoms = m_atoms.size();
            for (unsigned j = 0; j < num_atoms; ++j) {
                atom* a = m_atoms[j];
                if (a && a->is_ineq_atom()) {
                    ineq_atom const& a1 = *to_ineq_atom(a);
                    unsigned sz = a1.size();
                    ps.reset();
                    even.reset();
                    bool change = false;
                    auto k = a1.get_kind();
                    for (unsigned i = 0; i < sz; ++i) {
                        poly * po = a1.p(i);
                        m_pm.substitute(po, x, q, p, pr);
                        change |= pr != po;
                        if (m_pm.is_zero(pr)) {
                            ps.reset();
                            even.reset();
                            ps.push_back(pr);
                            even.push_back(false);
                            break;
                        }
                        if (m_pm.is_const(pr)) {
                            if (!a1.is_even(i) && m_pm.m().is_neg(m_pm.coeff(pr, 0))) {
                                k = atom::flip(k);
                            }
                            continue;
                        }
                        ps.push_back(pr);                                
                        even.push_back(a1.is_even(i));
                    }        
                    if (!change) continue;
                    literal l = mk_ineq_literal(k, ps.size(), ps.data(), even.data()); 
                    lits.push_back(l);
                    if (a1.m_bool_var != l.var()) {                        
                        b2l.insert(a1.m_bool_var, l);
                    }
                }
            }
            is_sat = update_clauses(b2l);
            return is_sat;
        }


        bool update_clauses(u_map<literal> const& b2l) {
            bool is_sat = true;
            literal_vector lits;
            clause_vector to_delete;
            unsigned n = m_clauses.size();
            for (unsigned i = 0; i < n; ++i) {
                clause* c = m_clauses[i];
                lits.reset();
                bool changed = false;
                bool is_tautology = false;
                for (literal l : *c) {               
                    literal lit = null_literal;
                    if (b2l.find(l.var(), lit)) {
                        lit = l.sign() ? ~lit : lit;
                        if (lit == true_literal) {
                            is_tautology = true;
                        }
                        else if (lit != false_literal) {                            
                            lits.push_back(lit);
                        }
                        changed = true;
                    }
                    else {
                        lits.push_back(l);
                    }
                }
                if (changed) {
                    to_delete.push_back(c);
                    if (is_tautology) {
                        continue;
                    }
                    if (lits.empty()) {
                        is_sat = false;
                    }
                    else {
                        mk_clause(lits.size(), lits.data(), c->is_learned(), static_cast<_assumption_set>(c->assumptions()));
                    }
                }                        
            }        
            for (clause* c : to_delete) {
                del_clause(c, m_clauses);
            }
            return is_sat;
        }

        bool is_unit_ineq(clause const& c) const {
            return 
                c.size() == 1 &&
                m_atoms[c[0].var()] && 
                m_atoms[c[0].var()]->is_ineq_atom();
        }

        bool is_unit_eq(clause const& c) const {
            return 
                is_unit_ineq(c) && 
                !c[0].sign() && 
                m_atoms[c[0].var()]->is_eq();
        }

        /**
           \brief determine whether the clause is a comparison v > k or v < k', where k >= 0 or k' <= 0.
         */
        lbool is_cmp0(clause const& c, var& v) {
            if (!is_unit_ineq(c)) return l_undef;
            literal lit = c[0];
            ineq_atom const& a = *to_ineq_atom(m_atoms[lit.var()]);
            bool sign = lit.sign();
            poly * p0;
            if (!is_single_poly(a, p0)) return l_undef;
            if (m_pm.is_var(p0, v)) {
                if (!sign && a.get_kind() == atom::GT) {
                    return l_true;
                }
                if (!sign && a.get_kind() == atom::LT) {
                    return l_false;
                }
                return l_undef;
            }
            polynomial::scoped_numeral n(m_pm.m());
            if (m_pm.is_var_num(p0, v, n)) {
                // x - k > 0
                if (!sign && a.get_kind() == atom::GT && m_pm.m().is_nonneg(n)) {
                    return l_true;
                }
                // x + k < 0
                if (!sign && a.get_kind() == atom::LT && m_pm.m().is_nonpos(n)) {
                    return l_false;
                }
                // !(x + k > 0)
                if (sign && a.get_kind() == atom::GT && m_pm.m().is_pos(n)) {
                    return l_false;
                }
                // !(x - k < 0)
                if (sign && a.get_kind() == atom::LT && m_pm.m().is_neg(n)) {
                    return l_true;
                }
            }
            return l_undef;
        }

        bool is_single_poly(ineq_atom const& a, poly*& p) {
            unsigned sz = a.size();
            return sz == 1 && a.is_odd(0) && (p = a.p(0), true);
        }

        svector<lbool> m_var_signs;

        void init_var_signs() {
            m_var_signs.reset();
            for (clause* cp : m_clauses) {
                clause& c = *cp;
                var x = 0;
                lbool cmp = is_cmp0(c, x);
                switch (cmp) {
                case l_true:
                    m_var_signs.setx(x, l_true, l_undef);
                    break;
                case l_false:
                    m_var_signs.setx(x, l_false, l_undef);
                    break;
                default:
                    break;                
                }
            }
        }

        bool have_var_ge(poly const * p, var x) {
            var_vector curr;
            m_pm.vars(p, curr);
            for(var v: curr){
                if(v >= x){
                    return true;
                }
            }
            return false;
        }

        /**
           \brief returns true then c is an equality that is equivalent to v*p + q, 
           and p > 0, v does not occur in p, q.
        */
        bool solve_var(clause& c, var& v, polynomial_ref& p, polynomial_ref& q) {
            poly* p0;
            if (!is_unit_eq(c)) return false;
            ineq_atom & a = *to_ineq_atom(m_atoms[c[0].var()]);
            if (!is_single_poly(a, p0)) return false;
            // var mx = max_var(p0);
            // if (mx >= m_is_int.size()) return false;
            if(have_var_ge(p0, num_arith_vars())){
                return false;
            }
            var_vector curr_vars;
            m_pm.vars(p0, curr_vars);
            // for (var x = 0; x <= mx; ++x) {
            for(var x: curr_vars){
                if (m_is_int[x]) continue;
                if (1 == m_pm.degree(p0, x)) {                    
                    p = m_pm.coeff(p0, x, 1, q);
                    if (!m_pm.is_const(p))
                        break;
                    switch (m_pm.sign(p, m_var_signs)) {
                    case l_true:
                        v = x;
                        return true;
                    case l_false:
                        v = x;
                        p = -p;
                        q = -q;
                        return true;
                    default:
                        break;
                    }
                }
            }
            return false;
        }        

        // -----------------------
        //
        // Pretty printing
        //
        // -----------------------
        
        std::ostream& display_num_assignment(std::ostream & out, display_var_proc const & proc) const {
            for (var x = 0; x < num_arith_vars(); x++) {
                if (m_assignment.is_assigned(x)) {
                    out << "var " << x << " ";
                    proc(out, x);
                    out << " -> ";
                    m_am.display_decimal(out, m_assignment.value(x));
                    out << "\n";
                }
            }
            return out;
        }

        std::ostream& display_bool_assignment(std::ostream & out) const {
            unsigned sz = m_atoms.size();
            for (bool_var b = 0; b < sz; b++) {
                if (m_atoms[b] == nullptr && m_bvalues[b] != l_undef) {
                    out << "b" << b << " -> " << (m_bvalues[b] == l_true ? "true" : "false") << "\n";
                }
                else if (m_atoms[b] != nullptr && m_bvalues[b] != l_undef) {
                    display(out << "b" << b << " ", *m_atoms[b]) << " -> " << (m_bvalues[b] == l_true ? "true" : "false") << "\n";
                }
            }
            return out;
        }

        std::ostream & display_bool_convert(std::ostream & out) const {
            out << "display pure bool vars\n";
            for(unsigned i = 0; i < m_pure_bool_vars.size(); i++){
                out << "bool var " << i << " -> " << m_pure_bool_vars[i] << std::endl;
            }
            return out;
        }

        bool display_mathematica_assignment(std::ostream & out) const {
            bool first = true;
            for (var x = 0; x < num_arith_vars(); x++) {
                if (m_assignment.is_assigned(x)) {
                    if (first)
                        first = false;
                    else
                        out << " && ";
                    out << "x" << x << " == ";
                    m_am.display_mathematica(out, m_assignment.value(x));
                }
            }
            return !first;
        }

        std::ostream& display_num_assignment(std::ostream & out) const { 
            return display_num_assignment(out, m_display_var);
        }

        std::ostream& display_assignment(std::ostream& out) const {
            out << "Display Assignment" << std::endl;
            display_bool_assignment(out);
            display_num_assignment(out);
            return out;
        }

        std::ostream& display(std::ostream& out, justification j) const {
            switch (j.get_kind()) {
            case justification::CLAUSE:
                display(out, *j.get_clause()) << "\n";
                break;
            case justification::LAZY: {
                lazy_justification const& lz = *j.get_lazy();
                display_not(out, lz.num_lits(), lz.lits()) << "\n";
                for (unsigned i = 0; i < lz.num_clauses(); ++i) {
                    display(out, lz.clause(i)) << "\n";
                }
                break;
            }
            default:
                out << j.get_kind() << "\n";
                break;                
            }
            return out;
        }
       
        std::ostream& display(std::ostream & out, ineq_atom const & a, display_var_proc const & proc, bool use_star = false) const {
            unsigned sz = a.size();
            for (unsigned i = 0; i < sz; i++) {
                if (use_star && i > 0)
                    out << "*";
                bool is_even = a.is_even(i);
                if (is_even || sz > 1)
                    out << "(";
                m_pm.display(out, a.p(i), proc, use_star);
                if (is_even || sz > 1)
                    out << ")";
                if (is_even)
                    out << "^2";
            }
            switch (a.get_kind()) {
            case atom::LT: out << " < 0"; break;
            case atom::GT: out << " > 0"; break;
            case atom::EQ: out << " = 0"; break;
            default: UNREACHABLE(); break;
            }
            return out;
        }
        
        std::ostream& display_mathematica(std::ostream & out, ineq_atom const & a) const {
            unsigned sz = a.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0)
                    out << "*";
                bool is_even = a.is_even(i);
                if (sz > 1)
                    out << "(";
                if (is_even)
                    out << "(";
                m_pm.display(out, a.p(i), display_var_proc(), true);
                if (is_even)
                    out << "^2)";
                if (sz > 1)
                    out << ")";
            }
            switch (a.get_kind()) {
            case atom::LT: out << " < 0"; break;
            case atom::GT: out << " > 0"; break;
            case atom::EQ: out << " == 0"; break;
            default: UNREACHABLE(); break;
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, ineq_atom const & a, display_var_proc const & proc) const {
            switch (a.get_kind()) {
            case atom::LT: out << "(< "; break;
            case atom::GT: out << "(> "; break;
            case atom::EQ: out << "(= "; break;
            default: UNREACHABLE(); break;
            }
            unsigned sz = a.size();
            if (sz > 1)
                out << "(* ";
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0) out << " ";
                if (a.is_even(i)) {
                    out << "(* ";
                    m_pm.display_smt2(out, a.p(i), proc);
                    out << " ";
                    m_pm.display_smt2(out, a.p(i), proc);
                    out << ")";
                }
                else {
                    m_pm.display_smt2(out, a.p(i), proc);
                }
            }
            if (sz > 1)
                out << ")";
            out << " 0)";
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, root_atom const & a, display_var_proc const & proc) const {
            return display(out, a, proc);
        }
        
        std::ostream& display(std::ostream & out, root_atom const & a, display_var_proc const & proc) const {
            proc(out, a.x());
            switch (a.get_kind()) {
            case atom::ROOT_LT: out << " < "; break;
            case atom::ROOT_GT: out << " > "; break;
            case atom::ROOT_LE: out << " <= "; break;
            case atom::ROOT_GE: out << " >= "; break;
            case atom::ROOT_EQ: out << " = "; break;
            default: UNREACHABLE(); break;
            }
            out << "root[" << a.i() << "](";
            m_pm.display(out, a.p(), proc);
            out << ")";
            return out;
        }

        struct mathematica_var_proc : public display_var_proc {
            var m_x;
        public:
            mathematica_var_proc(var x):m_x(x) {}
            std::ostream& operator()(std::ostream & out, var x) const override {
                if (m_x == x)
                    return out << "#1";
                else
                    return out << "x" << x; 
            }
        };

        std::ostream& display_mathematica(std::ostream & out, root_atom const & a) const {
            out << "x" << a.x();
            switch (a.get_kind()) {
            case atom::ROOT_LT: out << " < "; break;
            case atom::ROOT_GT: out << " > "; break;
            case atom::ROOT_LE: out << " <= "; break;
            case atom::ROOT_GE: out << " >= "; break;
            case atom::ROOT_EQ: out << " == "; break;
            default: UNREACHABLE(); break;
            }
            out << "Root[";
            m_pm.display(out, a.p(), mathematica_var_proc(a.x()), true);
            out << " &, " << a.i() << "]";
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, root_atom const & a) const {
            NOT_IMPLEMENTED_YET();
            return out;
        }
        
        std::ostream& display(std::ostream & out, atom const & a, display_var_proc const & proc) const {
            if (a.is_ineq_atom())
                return display(out, static_cast<ineq_atom const &>(a), proc);
            else
                return display(out, static_cast<root_atom const &>(a), proc);
        }

        std::ostream& display(std::ostream & out, atom const & a) const {
            return display(out, a, m_display_var);
        }

        std::ostream& display_mathematica(std::ostream & out, atom const & a) const {
            if (a.is_ineq_atom())
                return display_mathematica(out, static_cast<ineq_atom const &>(a));
            else
                return display_mathematica(out, static_cast<root_atom const &>(a));
        }

        std::ostream& display_smt2(std::ostream & out, atom const & a, display_var_proc const & proc) const {
            if (a.is_ineq_atom())
                return display_smt2(out, static_cast<ineq_atom const &>(a), proc);
            else
                return display_smt2(out, static_cast<root_atom const &>(a), proc);
        }

        std::ostream& display_atom(std::ostream & out, bool_var b, display_var_proc const & proc) const {
            if (b == 0)
                out << "true";
            else if (m_atoms[b] == 0)
                out << "b" << b;
            else
                display(out, *(m_atoms[b]), proc);
            return out;
        }

        std::ostream& display_atom(std::ostream & out, bool_var b) const {
            return display_atom(out, b, m_display_var);
        }

        std::ostream& display_mathematica_atom(std::ostream & out, bool_var b) const {
            if (b == 0)
                out << "(0 < 1)";
            else if (m_atoms[b] == 0)
                out << "b" << b;
            else
                display_mathematica(out, *(m_atoms[b]));
            return out;
        }

        std::ostream& display_smt2_atom(std::ostream & out, bool_var b, display_var_proc const & proc) const {
            if (b == 0)
                out << "true";
            else if (m_atoms[b] == 0)
                out << "b" << b;
            else
                display_smt2(out, *(m_atoms[b]), proc);
            return out;
        }

        std::ostream& display(std::ostream & out, literal l, display_var_proc const & proc) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "!";
                if (m_atoms[b] != 0)
                    out << "(";
                display_atom(out, b, proc);
                if (m_atoms[b] != 0)
                    out << ")";
            }
            else {
                display_atom(out, l.var(), proc);
            }
            return out;
        }

        std::ostream& display(std::ostream & out, literal l) const {
            return display(out, l, m_display_var);
        }

        std::ostream& display_smt2(std::ostream & out, literal l) const {
            return display_smt2(out, l, m_display_var);
        }

        std::ostream& display_mathematica(std::ostream & out, literal l) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "!";
                if (m_atoms[b] != 0)
                    out << "(";
                display_mathematica_atom(out, b);
                if (m_atoms[b] != 0)
                    out << ")";
            }
            else {
                display_mathematica_atom(out, l.var());
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, literal l, display_var_proc const & proc) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "(not ";
                display_smt2_atom(out, b, proc);
                out << ")";
            }
            else {
                display_smt2_atom(out, l.var(), proc);
            }
            return out;
        }
            
        std::ostream& display_assumptions(std::ostream & out, _assumption_set s) const {
            vector<assumption, false> deps;
            m_asm.linearize(s, deps);
            bool first = true;
            for (auto dep : deps) {
                if (first) first = false; else out << " ";
                if (m_display_assumption) (*m_display_assumption)(out, dep); 
            }
            return out;
        }
        
        std::ostream& display(std::ostream & out, unsigned num, literal const * ls, display_var_proc const & proc) const {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " or ";
                display(out, ls[i], proc);
            }
            return out;
        }

        std::ostream& display(std::ostream & out, unsigned num, literal const * ls) const {
            return display(out, num, ls, m_display_var);
        }

        std::ostream& display_not(std::ostream & out, unsigned num, literal const * ls, display_var_proc const & proc) const {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " or ";
                display(out, ~ls[i], proc);
            }
            return out;
        }

        std::ostream& display_not(std::ostream & out, unsigned num, literal const * ls) const {
            return display_not(out, num, ls, m_display_var);
        }
        
        std::ostream& display(std::ostream & out, scoped_literal_vector const & cs) {
            return display(out, cs.size(), cs.data(), m_display_var);
        }

        std::ostream& display(std::ostream & out, clause const & c, display_var_proc const & proc) const {
            if (c.assumptions() != nullptr) {
                display_assumptions(out, static_cast<_assumption_set>(c.assumptions()));
                out << " |- ";
            }
            return display(out, c.size(), c.data(), proc);
        }

        std::ostream& display(std::ostream & out, clause const & c) const {
            return display(out, c, m_display_var);
        }

        std::ostream& display_smt2(std::ostream & out, unsigned num, literal const * ls, display_var_proc const & proc) const {
            if (num == 0) {
                out << "false";
            }
            else if (num == 1) {
                display_smt2(out, ls[0], proc);
            }
            else {
                out << "(or";
                for (unsigned i = 0; i < num; i++) {
                    out << " ";
                    display_smt2(out, ls[i], proc);
                }
                out << ")";
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out, clause const & c, display_var_proc const & proc = display_var_proc()) const {
            return display_smt2(out, c.size(), c.data(), proc);
        }

        std::ostream& display_abst(std::ostream & out, literal l) const {
            if (l.sign()) {
                bool_var b = l.var();
                out << "!";
                if (b == true_bool_var)
                    out << "true";
                else
                    out << "b" << b;
            }
            else {
                out << "b" << l.var();
            }
            return out;
        }

        std::ostream& display_abst(std::ostream & out, unsigned num, literal const * ls) const {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " or ";
                display_abst(out, ls[i]);
            }
            return out;
        }

        std::ostream& display_abst(std::ostream & out, scoped_literal_vector const & cs) const {
            return display_abst(out, cs.size(), cs.data());
        }

        std::ostream& display_abst(std::ostream & out, clause const & c) const {
            return display_abst(out, c.size(), c.data());
        }

        std::ostream& display_mathematica(std::ostream & out, clause const & c) const {
            out << "(";
            unsigned sz = c.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0)
                    out << " || ";
                display_mathematica(out, c[i]);
            }
            out << ")";
            return out;
        }

        // Debugging support:
        // Display generated lemma in Mathematica format.
        // Mathematica must reduce lemma to True (modulo resource constraints).
        std::ostream& display_mathematica_lemma(std::ostream & out, unsigned num, literal const * ls, bool include_assignment = false) const {
            out << "Resolve[ForAll[{";
            // var definition
            for (unsigned i = 0; i < num_arith_vars(); i++) {
                if (i > 0)
                    out << ", ";
                out << "x" << i;
            }
            out << "}, ";
            if (include_assignment) {
                out << "!(";
                if (!display_mathematica_assignment(out))
                    out << "0 < 1"; // nothing was printed
                out << ") || ";
            }
            for (unsigned i = 0; i < num; i++) {
                if (i > 0)
                    out << " || ";
                display_mathematica(out, ls[i]);
            }
            out << "], Reals]\n"; // end of exists
            return out;
        }
        
        std::ostream& display(std::ostream & out, clause_vector const & cs, display_var_proc const & proc) const {
            for (clause* c : cs) {
                display(out, *c, proc) << "\n";
            }
            return out;
        }

        std::ostream& display(std::ostream & out, clause_vector const & cs) const {
            return display(out, cs, m_display_var);
        }

        std::ostream& display_mathematica(std::ostream & out, clause_vector const & cs) const {            
            unsigned sz = cs.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i > 0) out << ",\n";
                display_mathematica(out << " ", *(cs[i]));
            }
            return out;
        }

        std::ostream& display_abst(std::ostream & out, clause_vector const & cs) const {
            for (clause* c : cs) {
                display_abst(out, *c) << "\n";
            }
            return out;
        }

        std::ostream& display(std::ostream & out, display_var_proc const & proc) const {
            display(out, m_clauses, proc);
            if (!m_learned.empty()) {
                display(out << "Lemmas:\n", m_learned, proc);
            }
            return out;
        }

        std::ostream& display_mathematica(std::ostream & out) const {
            return display_mathematica(out << "{\n", m_clauses) << "}\n";
        }

        std::ostream& display_abst(std::ostream & out) const {
            display_abst(out, m_clauses);
            if (!m_learned.empty()) {
                display_abst(out << "Lemmas:\n", m_learned);
            }
            return out;
        }

        std::ostream& display(std::ostream & out) const {
            display(out, m_display_var);
            display_assignment(out << "assignment:\n");
            return out << "---\n";
        }

        std::ostream& display_vars(std::ostream & out) const {
            for (unsigned i = 0; i < num_arith_vars(); i++) {
                out << i << " -> "; m_display_var(out, i); out << "\n";
            }
            return out;
        }

        std::ostream& display_hybrid_var(std::ostream &out, hybrid_var v) const {
            if(v == null_var) {
                out << "null_var";
                return out;
            }
            if(hybrid_is_arith(v)) {
                m_display_var(out, hybrid2arith(v));
            } else {
                display_atom(out, m_pure_bool_vars[v]);
            }
            return out;
        }

        std::ostream& display_smt2_arith_decls(std::ostream & out) const {
            unsigned sz = m_is_int.size();
            for (unsigned i = 0; i < sz; i++) {
                if (m_is_int[i])
                    out << "(declare-fun x" << i << " () Int)\n";
                else
                    out << "(declare-fun x" << i << " () Real)\n";
            }
            return out;
        }

        std::ostream& display_smt2_bool_decls(std::ostream & out) const {
            unsigned sz = m_atoms.size();
            for (unsigned i = 0; i < sz; i++) {
                if (m_atoms[i] == nullptr)
                    out << "(declare-fun b" << i << " () Bool)\n";
            }
            return out;
        }

        std::ostream& display_smt2(std::ostream & out) const {
            display_smt2_bool_decls(out);
            display_smt2_arith_decls(out);
            out << "(assert (and true\n";
            for (clause* c : m_clauses) {
                display_smt2(out, *c) << "\n";
            }
            out << "))\n" << std::endl;
            return out;
        }

        std::ostream & display_order_mode(std::ostream & out) const {
            #if DYNAMIC_MODE == UNIFORM_VSIDS
                out << "-----------------uniform mode-----------------\n";
            #elif DYNAMIC_MODE == BOOL_FIRST_VSIDS
                out << "-----------------bool first mode-----------------\n";
            #elif DYNAMIC_MODE == THEORY_FIRST_VSIDS
                out << "-----------------theory first mode-----------------\n";
            #elif DYNAMIC_MODE == ORIGIN_STATIC_BOOL_FIRST_MODE
                out << "-----------------origin static bool first mode-----------------\n";
            #elif DYNAMIC_MODE == RANDOM_MODE
                out << "-----------------random mode-----------------\n";
            #else
                UNREACHABLE();
            #endif

            return out;
        }

        static inline std::string bool2str(bool b) {
            return b ? "true" : "false";
        }

        std::ostream & display_status(std::ostream & out) const {
            out << "Display Status" << std::endl;
            out << "m_hk: " << m_hk << std::endl;
            out << "stage: " << m_scope_stage << std::endl;
            out << "level: " << m_scope_lvl << std::endl;
            display_assignment(out);
            display_trails(out);
            display_infeasible_set(out);
            display_arith_unit_clauses(out);
            display_arith_unit_atoms(out);
            return out;
        }

        std::ostream & display_arith_unit_clauses(std::ostream & out) const {
            for(var v = 0; v < num_arith_vars(); v++) {
                if(m_arith_unit_clauses[v].size() + m_arith_unit_learned[v].size() > 0) {
                    m_display_var(out, v);
                    out << " -> unit clause: ";
                    for(unsigned idx: m_arith_unit_clauses[v]) {
                        out << idx << " ";
                    }
                    out << std::endl;
                    out << " -> unit learned: ";
                    for(unsigned idx: m_arith_unit_learned[v]) {
                        out << idx << " ";
                    }
                    out << std::endl;
                }
            }
            return out;
        }

        std::ostream & display_arith_unit_atoms(std::ostream & out) const {
            for(var v = 0; v < num_arith_vars(); v++) {
                if(m_arith_unit_atom[v].size() > 0) {
                    m_display_var(out, v);
                    out << " -> unit atom: ";
                    for(unsigned idx: m_arith_unit_atom[v]) {
                        out << idx << " ";
                    }
                    out << std::endl;
                }
            }
            return out;
        }

        std::ostream & display_infeasible_set(std::ostream & out) const {
            for(var v = 0; v < num_arith_vars(); v++) {
                m_display_var(out, v);
                out << " -> ";
                m_ism.display(out, m_infeasible[v]);
                out << "\n";
            }
            return out;
        }

        std::ostream & display_trails(std::ostream & out) const {
            out << "================== Display Trails ==================\n";
            unsigned stage_cnt = 0, level_cnt = 0;
            for(auto ele: m_trail){
                switch(ele.m_kind){
                    case trail::BVAR_ASSIGNMENT:
                        out << "[BVAR ASSIGNMENT]: "; display_atom(out, ele.m_x); 
                        if(m_atoms[ele.m_x] == nullptr){
                            out << " -> bool_var " << m_pure_bool_convert[ele.m_x];
                        }
                        out << std::endl;
                        break;

                    case trail::INFEASIBLE_UPDT:
                        out << "[INFEASIBLE UPDT]: "; m_ism.display(out, ele.m_old_set); out << std::endl;
                        break;

                    case trail::NEW_LEVEL:
                        out << "[NEW LEVEL]\n";
                        break;
                    
                    case trail::NEW_STAGE:
                        out << "[NEW STAGE]\n";
                        break;

                    case trail::UPDT_EQ:
                        out << "[UPDT_EQ] "; display(out, ele.m_old_eq);
                        break;

                    case trail::ARITH_ASSIGNMENT:
                        out << "[ARITH ASSIGNMENT]: ";
                        m_display_var(out, ele.m_x); out << " -> ";
                        m_am.display(out, m_assignment.value(ele.m_x));
                        out << std::endl;
                        break;

                    case trail::SEMANTICS_DECISION:
                        out << "[START SEMANTICS DECISION]: " << ele.m_x << std::endl;
                        break;

                    case trail::BRANCH:
                        out << "[BRANCH] old m_hk: " << ele.m_x << "  ";
                        display_hybrid_var(out, ele.m_x) << "    ";
                        out << "new m_hk: " << ele.m_x2 << " ";
                        display_hybrid_var(out, ele.m_x2) << std::endl;
                        break;

                    default:
                        UNREACHABLE();
                }
            }
            out << "================== Trails Done ==================\n";
            return out;
        }

        std::ostream & display_var_vector(std::ostream & out, var_vector const & vec) const {
            for(auto ele: vec){
                out << ele << " ";
            }
            out << std::endl;
            return out;
        }

        std::ostream & display_clause_vector(std::ostream & out, unsigned_vector const & vec) const {
            for(unsigned i = 0; i < vec.size(); i++){
                display(out, *m_clauses[vec[i]]); out << std::endl;
            }
            return out;
        }

        std::ostream & display_clauses(std::ostream & out) const {
            out << "display clauses\n";
            for(unsigned i = 0; i < m_clauses.size(); i++){
                if(!m_deleted_clauses.contains(i)) {
                    display(out, *m_clauses[i]); out << std::endl;
                }
            }
            return out;
        }

        std::ostream & display_hybrid_trail(std::ostream & out) const {
            for(hybrid_var v: m_hybrid_trail) {
                if(hybrid_is_bool(v) && m_decision_bools.contains(v)) {
                    out << "[d]";
                }
                display_hybrid_var(out, v) << " ";
            }
            out << std::endl;
            return out;
        }

        std::string lbool2str(lbool r) const {
            switch(r){
                case l_true:
                    return "l_true";

                case l_false:
                    return "l_false";

                case l_undef:
                    return "l_undef";

                default:
                    UNREACHABLE();
            }
        }

        std::ostream & show_all_assignment(std::ostream & out) const {
            out << "show all assignment\n";
            m_assignment.display(out);
            for(unsigned i = 0; i < m_pure_bool_vars.size(); i++){
                out << "bool var " << m_pure_bool_vars[i] << " -> " << lbool2str(m_bvalues[m_pure_bool_vars[i]]) << std::endl;
            }
            return out;
        }

        std::ostream & display_assigned_vars(std::ostream & out) const {
            out << "display assigned vars " << "(size: " << m_hybrid_trail.size() << ")" << std::endl;
            if(m_hybrid_trail.empty()) {
                out << "EMPTY\n";
            } else {
                for(hybrid_var v: m_hybrid_trail) {
                    display_hybrid_var(out, v) << " ";
                }
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_hybrid_activity(std::ostream & out) const {
            for(hybrid_var v = 0; v < m_hybrid_activity.size(); v++) {
                out << "var " << v << " -> " << m_hybrid_activity[v] << std::endl;
            }
            return out;
        }

        std::ostream & display_var_stage(std::ostream & out) const {
            out << "display hybrid var stage:\n";
            for(hybrid_var v = 0; v < m_hybrid_find_stage.size(); v++) {
                out << "hybrid var: " << v << " -> " << m_hybrid_find_stage[v] << std::endl;
            }
            return out;
        }
    };
    
    solver::solver(reslimit& rlim, params_ref const & p, bool incremental) {
        m_ctx = alloc(ctx, rlim, p, incremental);
        m_imp = alloc(imp, *this, *m_ctx);
    }

    solver::solver(ctx& ctx) {
        m_ctx = nullptr;
        m_imp = alloc(imp, *this, ctx);
    }
        
    solver::~solver() {
        dealloc(m_imp);
        dealloc(m_ctx);
    }

    lbool solver::check() {
        return m_imp->check();
    }

    lbool solver::check(literal_vector& assumptions) {
        return m_imp->check(assumptions);
    }

    void solver::get_core(vector<assumption, false>& assumptions) {
        return m_imp->get_core(assumptions);
    }

    void solver::reset() {
        m_imp->reset();
    }

    void solver::updt_params(params_ref const & p) {
        m_imp->updt_params(p);
    }

    void solver::collect_param_descrs(param_descrs & d) {
        algebraic_numbers::manager::collect_param_descrs(d);
        nlsat_params::collect_param_descrs(d);
    }

    unsynch_mpq_manager & solver::qm() {
        return m_imp->m_qm;
    }
        
    anum_manager & solver::am() {
        return m_imp->m_am;
    }

    pmanager & solver::pm() {
        return m_imp->m_pm;
    }

    void solver::set_display_var(display_var_proc const & proc) {
        m_imp->m_display_var.m_proc = &proc;
    }

    void solver::set_display_assumption(display_assumption_proc const& proc) {
        m_imp->m_display_assumption = &proc;
    }
    
    unsigned solver::num_bool_vars() const {
        return m_imp->num_bool_vars();
    }

    unsigned solver::num_arith_vars() const {
        return m_imp->num_arith_vars();
    }

    bool solver::is_int(var x) const {
        return m_imp->is_int(x);
    }

    bool_var solver::mk_bool_var() {
        DTRACE(std::cout << "make bool var" << std::endl;);
        auto res = m_imp->mk_bool_var();
        DTRACE(std::cout << "make bool var done" << std::endl;);
        return res;
    }
    
    literal solver::mk_true() {
        return literal(0, false);
    }

    atom * solver::bool_var2atom(bool_var b) {
        return m_imp->m_atoms[b];
    }

    void solver::vars(literal l, var_vector& vs) {
        m_imp->vars(l, vs);
    }

    atom_vector const& solver::get_atoms() {
        return m_imp->m_atoms;
    }

    atom_vector const& solver::get_var2eq() {
        return m_imp->m_var2eq;
    }

    evaluator& solver::get_evaluator() {
        return m_imp->m_evaluator;
    }

    explain& solver::get_explain() {
        return m_imp->m_explain;
    }

    void solver::reorder(unsigned sz, var const* p) {
        m_imp->reorder(sz, p);
    }

    void solver::restore_order() {
        m_imp->restore_order();
    }

    void solver::set_rvalues(assignment const& as) {
        m_imp->m_assignment.copy(as);
    }

    void solver::get_rvalues(assignment& as) {
        as.copy(m_imp->m_assignment);
    }

    void solver::get_bvalues(svector<bool_var> const& bvars, svector<lbool>& vs) {
        vs.reset();
        for (bool_var b : bvars) {
            vs.reserve(b + 1, l_undef);
            if (!m_imp->m_atoms[b]) {
                vs[b] = m_imp->m_bvalues[b];
            }
        }
    }

    void solver::set_bvalues(svector<lbool> const& vs) {
        for (bool_var b = 0; b < vs.size(); ++b) {
            if (vs[b] != l_undef) {
                m_imp->m_bvalues[b] = vs[b];
                SASSERT(!m_imp->m_atoms[b]);
            }
        }
#if 0        
        m_imp->m_bvalues.reset();
        m_imp->m_bvalues.append(vs);
        m_imp->m_bvalues.resize(m_imp->m_atoms.size(), l_undef);        
        for (unsigned i = 0; i < m_imp->m_atoms.size(); ++i) {
            atom* a = m_imp->m_atoms[i];
            SASSERT(!a);
            if (a) {
                m_imp->m_bvalues[i] = to_lbool(m_imp->m_evaluator.eval(a, false));
            }
        }
#endif
    }
    
    var solver::mk_var(bool is_int) {
        DTRACE(std::cout << "make var" << std::endl;);
        var x = m_imp->mk_var(is_int);
        DTRACE(std::cout << "make var done" << std::endl;);
        return x;
    }
        
    bool_var solver::mk_ineq_atom(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even) {
        DTRACE(std::cout << "make ineq atom" << std::endl;);
        auto res = m_imp->mk_ineq_atom(k, sz, ps, is_even);
        DTRACE(std::cout << "make ineq atom done" << std::endl;);
        return res;
    }

    literal solver::mk_ineq_literal(atom::kind k, unsigned sz, poly * const * ps, bool const * is_even) {
        DTRACE(std::cout << "make literal" << std::endl;);
        auto res = m_imp->mk_ineq_literal(k, sz, ps, is_even);
        DTRACE(display(std::cout, res) << std::endl;
            std::cout << res.var() << std::endl;
        );
        DTRACE(std::cout << "make literal done" << std::endl;);
        return res;
    }

    bool_var solver::mk_root_atom(atom::kind k, var x, unsigned i, poly * p) {
        DTRACE(std::cout << "make root atom" << std::endl;);
        auto res = m_imp->mk_root_atom(k, x, i, p);
        DTRACE(std::cout << "make root atom done" << std::endl;);
        return res;
    }
    
    void solver::inc_ref(bool_var b) {
        m_imp->inc_ref(b);
    }

    void solver::dec_ref(bool_var b) {
        m_imp->dec_ref(b);
    }
        
    void solver::mk_clause(unsigned num_lits, literal * lits, assumption a) {
        DTRACE(std::cout << "make clause" << std::endl;);
        m_imp->mk_clause(num_lits, lits, a);
        DTRACE(std::cout << "make clause done" << std::endl;);
    }

    std::ostream& solver::display(std::ostream & out) const {
        return m_imp->display(out);
    }

    std::ostream& solver::display(std::ostream & out, literal l) const {
        return m_imp->display(out, l);
    }

    std::ostream& solver::display(std::ostream & out, unsigned n, literal const* ls) const {
        for (unsigned i = 0; i < n; ++i) {
            display(out, ls[i]);
            out << ";  ";
        }
        return out;
    }

    std::ostream& solver::display(std::ostream & out, literal_vector const& ls) const {
        return display(out, ls.size(), ls.data());
    }

    std::ostream& solver::display_smt2(std::ostream & out, literal l) const {
        return m_imp->display_smt2(out, l);
    }

    std::ostream& solver::display_smt2(std::ostream & out, unsigned n, literal const* ls) const {
        for (unsigned i = 0; i < n; ++i) {
            display_smt2(out, ls[i]);
            out << "  ";
        }
        return out;
    }

    std::ostream& solver::display_smt2(std::ostream & out, literal_vector const& ls) const {
        return display_smt2(out, ls.size(), ls.data());
    }

    std::ostream& solver::display(std::ostream & out, var x) const {
        return m_imp->m_display_var(out, x);
    }

    std::ostream& solver::display(std::ostream & out, atom const& a) const {
        return m_imp->display(out, a, m_imp->m_display_var);
    }

    display_var_proc const & solver::display_proc() const {
        return m_imp->m_display_var;
    }

    anum const & solver::value(var x) const {
        if (m_imp->m_assignment.is_assigned(x))
            return m_imp->m_assignment.value(x);
        return m_imp->m_zero;
    }
    
    lbool solver::bvalue(bool_var b) const {
        return m_imp->m_bvalues[b];
    }

    lbool solver::value(literal l) const {
        return m_imp->value(l);
    }

    bool solver::is_interpreted(bool_var b) const {
        return m_imp->m_atoms[b] != 0;
    }

    void solver::reset_statistics() {
        return m_imp->reset_statistics();
    }

    void solver::collect_statistics(statistics & st) {
        return m_imp->collect_statistics(st);
    }

    // dnlsat
    void solver::del_clause(clause * cls) {
        m_imp->del_clause(cls);
    }

    std::ostream & solver::display(std::ostream & out, clause const & cls) const {
        return m_imp->display(out, cls);
    }

    std::ostream & solver::display_bool_assignment(std::ostream & out) const {
        return m_imp->display_bool_assignment(out);
    }

    var solver::max_stage_var_poly(poly const* p) const {
        return m_imp->max_stage_var_poly(p);
    }

    unsigned solver::max_stage_poly(poly const* p) const {
        return m_imp->max_stage_poly(p);
    }

    unsigned solver::max_stage_literal(literal l) const {
        return m_imp->max_stage_literal(l);
    }

    unsigned solver::find_hybrid_var_stage(hybrid_var x) const {
        return m_imp->find_hybrid_var_stage(x);
    }

    var solver::max_stage_or_unassigned_ps(polynomial_ref_vector const& ps) const {
        return m_imp->max_stage_or_unassigned_ps(ps);
    }

    var solver::max_stage_or_unassigned_literals(unsigned num, literal const* ls) const {
        return m_imp->max_stage_or_unassigned_literals(num, ls);
    }

    var solver::max_stage_or_unassigned_atom(atom const* a) const {
        return m_imp->max_stage_or_unassigned_atom(a);
    }
    // dnlsat
};