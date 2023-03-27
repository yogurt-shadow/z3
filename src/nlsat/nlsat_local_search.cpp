#include "nlsat/nlsat_local_search.h"
#include "util/heap.h"

/**
 * * local search for nlsat on nonlinear real arithmetic
*/

namespace nlsat {
    struct ls_helper::imp {
        /**
         * * Basic Manager
        */
        anum_manager                       &                 m_am;
        pmanager                           &                 m_pm;
        interval_set_manager               &                 m_ism;
        evaluator                          &                 m_evaluator;
        polynomial::cache                  &                 m_cache;
        solver                             &                 m_solver;

        /**
         * * Assignment
        */
        assignment                         &                 m_assignment;
        svector<lbool>                     &                 m_bvalues;

        /**
         * * whether the value is fixed, i.e. can only be that point value
        */
        bool_vector                                          m_var_value_fixed;

        /**
         * ^ Const Anum
         * ^ Zero: 0
         * ^ One: 1
         * ^ Delta: 1/max
         * ^ Max: INT_MAX
         */
        anum                                                 m_zero, 
                                                             m_one, 
                                                             m_two,
                                                             m_ten, 
                                                             m_min;

        /**
         * * Arith Var
         */
        nra_arith_var_vector                                 m_arith_vars;
        // ^ arith vars that are visited
        var_table                                            m_vars_visited;
        // ^ literals that have been inserted from
        var_table                                            m_literal_added;
        
        /**
         * * Bool Var
         */
        nra_bool_var_vector                                  m_bool_vars;
        // ^ pure bool index --> atom index
        const bool_var_vector        &                       m_pure_bool_vars;
        // ^ atom index --> pure bool index
        const bool_var_vector        &                       m_pure_bool_convert;
        bool_var                                             m_max_bool_var;

        /**
         * * Literal
         */
        nra_literal_vector                                   m_nra_literals;
        var                                                  m_num_bool_literals;
        var                                                  m_num_arith_literals;
        
        literal_vector                                       m_literal_visited;
        // ^ used for set literal anum
        var_vector                                           m_literal_index_visited;
        // ^ store before sat information
        bool_vector                                          m_literal_before_sat;

        /**
         * * Count duplicated literals in various clauses
         * * Used for switch bool mode and arith mode
         */
        unsigned                                             m_num_unsat_literals;
        unsigned                                             m_num_bool_unsat_literals;

        /**
         * Clause
         */
        clause_vector                 &                      m_clauses;
        nra_clause_vector                                    m_nra_clauses;

        /** 
         * * Used for init arith var's infeasible set
        */
        // only contain just one arith variable
        var_table                                            m_unit_var_clauses;
        // only contain one literal
        var_table                                            m_unit_clauses;

        // unsat clauses (index)
        var_vector                                           m_unsat_clauses;
        // unsat clauses with pure bool var (index)
        var_table                                            m_unsat_clauses_bool;
        // sat clause with false literals (index)
        var_vector                                           m_sat_clause_with_false_literals;

        /**
         * * Weight
        */
        unsigned                                             m_total_clause_weight;
        const unsigned                                       smooth_probability = 3;

        /**
         * Atoms
         */
        const atom_vector                &                   m_atoms;

        /**
         * Information
         */
        var                                                  m_num_vars;
        var                                                  m_num_bool_vars;
        var                                                  m_num_literals;
        var                                                  m_num_clauses;

        /**
         * Random
         */
        unsigned                                             m_rand_seed;
        random_gen                                           m_rand;


        /**
         * * improvement and restart
         */
        unsigned                                             m_best_found_restart;
        unsigned                                             no_improve_cnt_bool;
        unsigned                                             no_improve_cnt_nra;
        unsigned                                             no_improve_cnt;
        unsigned                                             no_improve_cnt_mode;
        unsigned                                             m_best_found_cost_bool;
        unsigned                                             m_best_found_cost_nra;

        /**
         * * local search control
         */
        var                          &                       m_step;
        var                                                  m_outer_step;
        const unsigned                                       max_step        =       UINT_MAX;
        bool                                                 is_bool_search;
        bool                                                 is_random_walk;
        bool                                                 use_infeasible_st;
        unsigned                                             m_restart_count;

        /**
         * * Time
        */
        std::chrono::steady_clock::time_point                m_start_time;
        int                                                  m_time_label;
        double                                               m_best_cost_time;
        double                                               m_cutoff;

        /**
         * * Operation
         */
        bool_vector                                          m_bool_is_chosen;
        bool_var_vector                                      m_bool_operation_index;
        
        anum_table                                           m_nra_operation_table;
        var_vector                                           m_nra_operation_index;
        anum_vector                                          m_nra_operation_value;
        var_vector                                           m_nra_operation_literal_index;

        /**
         * * Statistics
        */
        // ^ no stuck
        unsigned                   &                         m_stuck;
        // ^ stuck step / whole step
        double                     &                         m_stuck_ratio;

        const substitute_value_vector &                      m_sub_value;

        /**
         * Equations
        */
        const unsigned_vector               &                m_equal_clauses;
        var_table                                            m_slacked_clauses;

        /**
         * @brief slack equations when we select a value which is not simpler then m_min
        */
        const bool                                           use_equation_slack = false;
        // currently 0.1
        anum                                                 m_slack_min;
        

        imp(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, svector<lbool> & bvalues, clause_vector & cls, atom_vector const & ats, unsigned_vector const & eq_cls, bool_var_vector const & pure_bool_vars, 
                         bool_var_vector const & pure_bool_convert, unsigned seed, unsigned & step, 
                         unsigned & stuck, double & ratio, substitute_value_vector const & vec)
        : m_am(am), m_pm(pm), m_ism(ism), m_evaluator(ev), m_assignment(ass), 
        m_clauses(cls), m_atoms(ats), m_equal_clauses(eq_cls), m_rand_seed(seed), m_solver(s), m_cutoff(1200), is_bool_search(false), is_random_walk(false),
        use_infeasible_st(true), m_restart_count(100), m_nra_operation_table(m_am, m_nra_operation_index, m_nra_operation_value),
        m_step(step), m_stuck(stuck), m_stuck_ratio(ratio), m_cache(cache), m_sub_value(vec),
        m_time_label(1), m_pure_bool_vars(pure_bool_vars), m_pure_bool_convert(pure_bool_convert), m_bvalues(bvalues)
        {
            set_const_anum();
            clear_statistics();
        }


        ~imp(){
            clear();
        }

        void clear_statistics(){
            m_stuck = 0;
            m_stuck_ratio = 0.0;
        }

        void clear(){
            LSTRACE(std::cout << "local search imp deleted\n";);
        }

        /**
         * * Initialize
         */
        void set_var_num(unsigned x){
            LSTRACE(tout << "set arith variable number: " << x << std::endl;
                std::cout << "start of set arith variable number\n";
            );
            m_num_vars = x;
            LSTRACE(display_vars(tout); display_clauses(tout););
            init_bool_vars();
            init_arith_vars();
            init_clauses();
            LSTRACE(tout << "end of set arith variable numbers" << std::endl;
                std::cout << "end of set arith variable number\n";
            );
        }

        /**
         * * fill in with pure bool vars
        */
        void init_bool_vars(){
            m_bool_vars.reset();
            m_num_bool_vars = m_pure_bool_vars.size();
            m_max_bool_var = m_pure_bool_vars.empty() ? null_var : m_pure_bool_vars.back();
            for(unsigned i = 0; i < m_num_bool_vars; i++) {
                // pure bool index, atom index
                m_bool_vars.push_back(new nra_bool_var(i, m_pure_bool_vars[i]));
            }
            m_bool_is_chosen.resize(m_num_bool_vars, false);
            LSTRACE(tout << "number of pure bool variables: " << m_num_bool_vars << std::endl;);
        }

        /**
         * * fill in with arith vars
        */
        void init_arith_vars(){
            m_arith_vars.reset();
            for(var v = 0; v < m_num_vars; v++){
                interval_set * curr_full = m_ism.mk_full();
                m_ism.inc_ref(curr_full);
                // m_ism.inc_ref(curr_empty);
                nra_arith_var * temp = new nra_arith_var(v, curr_full, nullptr);
                m_arith_vars.push_back(temp);
            }
        }

        void init_clauses(){
            LSTRACE(tout << "begin init clauses\n";);
            m_num_clauses = m_clauses.size();
            m_num_literals = 0;
            m_num_arith_literals = 0;
            m_num_bool_literals = 0;
            m_literal_visited.reset();
            m_nra_clauses.reset();
            m_nra_literals.reset();
            m_unit_var_clauses.reset();
            m_unit_clauses.reset();
            for(clause_index idx = 0; idx < m_clauses.size(); idx++){
                const clause & cls = *(m_clauses[idx]);
                LSTRACE(tout << "init clause "; m_solver.display(tout, cls); tout << std::endl;);
                nra_literal_vector curr_literals;
                var_table m_clause_vars;
                var_table m_clause_bool_vars;
                for(literal l: cls){
                    LSTRACE(tout << "pre-init literal "; m_solver.display(tout, l); tout << std::endl;);
                    literal_index lit_index = find_literal_vector(m_literal_visited, l);
                    nra_literal * m_literal;
                    if(lit_index == UINT_MAX){
                        // not register literal yet
                        init_literal(l);
                        m_literal = m_nra_literals.back();
                        lit_index = m_nra_literals.size() - 1;
                    }
                    else {
                        // registered literal
                        LSTRACE(tout << "already registered\n";);
                        SASSERT(m_nra_literals.size() > lit_index);
                        SASSERT(m_nra_literals[lit_index]->get_literal() == m_literal_visited[lit_index]);
                        m_literal = m_nra_literals[lit_index];
                    }
                    curr_literals.push_back(m_literal);
                    // bool literal
                    if(m_literal->is_bool()){
                        LSTRACE(tout << "bool literal, collect info for bool variables\n";);
                        SASSERT(m_literal->m_vars.empty());
                        bool_var b = m_literal->get_bool_index();
                        SASSERT(b != null_var);
                        nra_bool_var * b_var = m_bool_vars[b];
                        if(!m_clause_bool_vars.contains(b)){
                            m_clause_bool_vars.insert(b);
                            b_var->add_clause(idx);
                        }
                        b_var->add_literal_clause(lit_index, idx);
                        LSTRACE(tout << "bool var: " << b << std::endl;
                            tout << "bool literals: "; display_literal_set(tout, b_var->m_literals);
                            tout << std::endl;
                            tout << "bool lit_cls: \n"; display_clause_set(tout, b_var->m_lit_cls);
                            tout << std::endl;
                        );
                    }
                    else {
                        // loop arith var
                        LSTRACE(tout << "arith literal, collect info for arith variables\n";);
                        for(var v: m_literal->m_vars){
                            // LSTRACE(tout << "show size: " << m_arith_vars.size() << std::endl;);
                            if(!m_clause_vars.contains(v)){
                                m_clause_vars.insert(v);
                                m_arith_vars[v]->add_clause(idx);
                            }
                            m_arith_vars[v]->add_literal_clause(lit_index, idx);
                            LSTRACE(tout << "collect arith var " << v << " succeed\n";);
                        }
                    }
                }
                nra_clause * temp_clause = new nra_clause(idx, m_clauses[idx], curr_literals, m_clause_vars, m_clause_bool_vars);
                m_nra_clauses.push_back(temp_clause);
                // only one arith var and no bool literal
                if(m_clause_vars.size() == 1 && temp_clause->bool_size() == 0){
                    m_unit_var_clauses.insert(idx);
                    // var cls_var = *m_clause_vars.begin();
                    var cls_var = null_var;
                    for(var v: m_clause_vars){
                        cls_var = v;
                    }
                    SASSERT(cls_var != null_var);
                    nra_arith_var * curr_var = m_arith_vars[cls_var];
                    // curr_st = /\. st, stands for infeasible set of a variable
                    interval_set_ref curr_st(m_ism);
                    curr_st = m_ism.mk_full();
                    for(literal_index l_idx: temp_clause->m_literals){
                        nra_literal const * loop_literal = m_nra_literals[l_idx];
                        SASSERT(loop_literal->is_arith());
                        SASSERT(loop_literal->m_vars.size() == 1 && loop_literal->m_vars[0] == cls_var);
                        // we get infeasible set
                        interval_set_ref loop_st(m_ism);
                        loop_st = m_evaluator.infeasible_intervals(loop_literal->get_atom(), loop_literal->sign(), temp_clause->get_clause(), cls_var);
                        curr_st = m_ism.mk_intersection(curr_st, loop_st);
                    }
                    // infeasible set --> feasible set
                    curr_st = m_ism.mk_complement(curr_st);
                    // intersect feasible set
                    curr_var->m_feasible_st = m_ism.mk_intersection(curr_var->m_feasible_st, curr_st);
                }
                // only one literal
                if(temp_clause->size() == 1){
                    m_unit_clauses.insert(idx);
                }
                LSTRACE(tout << "end of this clause\n";);
            }
            LSTRACE(tout << "end of init clauses\n";);
            init_arith_infeasible_set();
            LSTRACE(tout << "show arith var's feasible set:\n";
                display_arith_intervals(tout);
            );
        }

        void analyze_problem() {
            for (clause_index i = 0; i < m_nra_clauses.size(); i++) {
                nra_clause const * cls = m_nra_clauses[i];
                for (literal_index j = 0; j < cls->m_literals.size(); j++) {
                    literal_index l_idx = cls->m_literals[j];
                    nra_literal const * l = m_nra_literals[l_idx];
                    if (l->is_arith()) {
                        ineq_atom const * a = l->get_atom();
                        // Display clauses containing equalities
                        // if (a->is_eq()) {
                        //     m_solver.display(std::cout, *cls->get_clause()); std::cout << std::endl;
                        // }
                    }
                }
            }
        }

        void init_arith_infeasible_set(){
            // m_var_init_st.reset();
            m_var_value_fixed.resize(m_arith_vars.size(), false);
            for(var v = 0; v < m_arith_vars.size(); v++){
                nra_arith_var * curr = m_arith_vars[v];
                curr->m_infeasible_st = m_ism.mk_complement(curr->m_feasible_st);
                if (curr->m_infeasible_st != nullptr) {
                    m_ism.inc_ref(curr->m_infeasible_st);
                }
            }
        }

        void init_literal(literal l){
            LSTRACE(tout << "init literal "; m_solver.display(tout, l); tout << std::endl;);
            bool is_bool = is_bool_literal(l);
            // bool literal: pure bool index
            // arith literal: null_var
            bool_var b_idx = is_bool ? m_pure_bool_convert[l.var()] : null_var;
            literal_index m_index = m_nra_literals.size();
            var_table m_vars;
            get_literal_vars(l, m_vars);
            LSTRACE(tout << "show literal vars: "; display_var_table(tout, m_vars); tout << std::endl;);
            nra_literal * temp = new nra_literal(m_index, b_idx, l, is_bool, m_vars, m_atoms[l.var()]);
            // LSCTRACE(m_atoms[l.var()] != nullptr,
            //     tout << "show literal atom:\n";
            //     m_solver.display(tout, *(temp->get_atom()));
            // );
            m_nra_literals.push_back(temp);
            m_literal_visited.push_back(l);
            m_num_literals++;
            if(is_bool){
                m_num_bool_literals++;
            }
            else {
                m_num_arith_literals++;
            }
            SASSERT(m_nra_literals.size() == m_literal_visited.size());
            LSTRACE(tout << "end of init literal\n";);
        }

        void init_arith_var_info() {
            // For each arith variable, compute the current infeasible set
            // for each clause and literal it appears in
            for (var v = 0; v < m_arith_vars.size(); v++){
                // std::cout << "considering variable " << v << std::endl;
                compute_arith_var_info(v);
                compute_boundary(v);
            }
        }

        void compute_arith_var_info(var v) {
            // Compute infeasible set information for variable
            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (unsigned i = 0; i < m_arith_var->m_clauses.size(); i++) {
                clause_index c_idx = m_arith_var->m_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                interval_set_ref result_st(m_ism);
                result_st = m_ism.mk_full();
                for (unsigned j = 0; j < curr_clause->m_arith_literals.size(); j++) {
                    literal_index l_idx = curr_clause->m_arith_literals[j];
                    nra_literal * curr_literal = m_nra_literals[l_idx];
                    if (!curr_literal->m_vars.contains(v)) {
                        continue;
                    }
                    // std::cout << "clause " << c_idx << " literal " << l_idx << std::endl;
                    interval_set_ref curr_st(m_ism);
                    curr_st = m_evaluator.infeasible_intervals(curr_literal->get_atom(), curr_literal->sign(), nullptr, v);
                    result_st = m_ism.mk_intersection(result_st, curr_st);
                }
                if (m_arith_var->m_clause_intervals[i] != nullptr) {
                    m_ism.dec_ref(m_arith_var->m_clause_intervals[i]);
                }
                m_arith_var->m_clause_intervals[i] = result_st;
                if (result_st != nullptr) {
                    m_ism.inc_ref(result_st);
                }
            }
        }

        void compute_arith_var_clause_info(var v, clause_index c_idx) {
            // Compute infeasible set information for variable
            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (unsigned i = 0; i < m_arith_var->m_clauses.size(); i++) {
                if (c_idx != m_arith_var->m_clauses[i]) {
                    continue;
                }
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                interval_set_ref result_st(m_ism);
                result_st = m_ism.mk_full();
                for (unsigned j = 0; j < curr_clause->m_arith_literals.size(); j++) {
                    literal_index l_idx = curr_clause->m_arith_literals[j];
                    nra_literal * curr_literal = m_nra_literals[l_idx];
                    if (!curr_literal->m_vars.contains(v)) {
                        continue;
                    }
                    // std::cout << "clause " << c_idx << " literal " << l_idx << std::endl;
                    interval_set_ref curr_st(m_ism);
                    curr_st = m_evaluator.infeasible_intervals(curr_literal->get_atom(), curr_literal->sign(), nullptr, v);
                    result_st = m_ism.mk_intersection(result_st, curr_st);
                }
                if (m_arith_var->m_clause_intervals[i] != nullptr) {
                    m_ism.dec_ref(m_arith_var->m_clause_intervals[i]);
                }
                m_arith_var->m_clause_intervals[i] = result_st;
                if (result_st != nullptr) {
                    m_ism.inc_ref(result_st);
                }
            }
        }

        void compute_boundary(var v) {
            // Compute boundary information for variable
            // std::cout << "compute boundary for " << v << std::endl;
            nra_arith_var * m_arith_var = m_arith_vars[v];
            m_arith_var->m_start_score = 0;
            m_arith_var->m_boundaries.reset();

            // If variable has infeasible set, add it with large weight
            if (use_infeasible_st) {
                if (m_arith_var->m_infeasible_st != nullptr) {
                    m_ism.add_boundaries(m_arith_var->m_infeasible_st, m_arith_var->m_boundaries,
                                        m_arith_var->m_start_score, INT_MAX / 2, null_var);
                }
            }

            for (unsigned i = 0; i < m_arith_var->m_clauses.size(); i++) {
                clause_index c_idx = m_arith_var->m_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];

                // std::cout << "clause " << c_idx << " weight " << curr_clause->get_weight() << std::endl;
                unsigned before_sat_count = curr_clause->get_sat_count();

                interval_set const * s = m_arith_var->m_clause_intervals[i];
                if (s == nullptr) {
                    continue;
                }
                if (before_sat_count > 0) {
                    // Potential break case, test whether some other literals are true
                    bool always_sat = false;
                    for (unsigned j = 0; j < curr_clause->m_arith_literals.size(); j++) {
                        literal_index l_idx = curr_clause->m_arith_literals[j];
                        nra_literal * curr_literal = m_nra_literals[l_idx];
                        if (curr_literal->get_sat_status() && !curr_literal->m_vars.contains(v)) {
                            always_sat = true;
                        }
                    }
                    for (unsigned j = 0; j < curr_clause->m_bool_literals.size(); j++) {
                        literal_index l_idx = curr_clause->m_bool_literals[j];
                        nra_literal * curr_literal = m_nra_literals[l_idx];
                        if (curr_literal->get_sat_status()) {
                            always_sat = true;
                        }
                    }
                    if (always_sat) {
                        continue;
                    }
                    // break case: infeasible intervals decrease score by 1
                    // std::cout << "break" << std::endl;
                    // m_ism.display(std::cout, s);
                    // std::cout << std::endl;
                    m_ism.add_boundaries(s, m_arith_var->m_boundaries, m_arith_var->m_start_score, curr_clause->get_weight(), c_idx);
                }

                if (before_sat_count == 0) {
                    // make case: feasible intervals increase score by 1
                    // std::cout << "make" << std::endl;
                    // m_ism.display(std::cout, s);
                    // std::cout << std::endl;
                    m_arith_var->m_start_score += curr_clause->get_weight();
                    m_ism.add_boundaries(s, m_arith_var->m_boundaries, m_arith_var->m_start_score, curr_clause->get_weight(), c_idx);
                }
            }
            std::sort(m_arith_var->m_boundaries.begin(), m_arith_var->m_boundaries.end(), lt_anum_boundary(m_am));
            // int score = m_arith_var->m_start_score;
            // std::cout << "start " << score << std::endl;
            // for (unsigned j = 0; j < m_arith_var->m_boundaries.size(); j++) {
            //     score += m_arith_var->m_boundaries[j].score;
            //     m_am.display(std::cout, m_arith_var->m_boundaries[j].value);
            //     std::cout << " " << m_arith_var->m_boundaries[j].is_open << " " << score << std::endl;
            // }
        }

        int get_best_arith_score(var v) {
            // Obtain the best score for variable v. Scores less than INT_MIN / 4
            // must be due to infeasible set of a variable, and hence discarded.
            nra_arith_var * m_arith_var = m_arith_vars[v];
            int score = m_arith_var->m_start_score;
            if (m_arith_var->m_boundaries.size() == 0) {
                return INT_MIN;
            }
            int best_score = score;
            for (unsigned i = 0; i < m_arith_var->m_boundaries.size(); i++) {
                score += m_arith_var->m_boundaries[i].score;
                if (score > best_score) {
                    best_score = score;
                }
            }
            if (best_score < INT_MIN / 4) {
                return INT_MIN;
            }
            return best_score;
        }

        bool contains_value(interval_set const * s, anum const & val) {
            // Whether interval set s contains val.
            interval_set_ref pt_val(m_ism);
            pt_val = m_ism.mk_point_interval(val);
            return m_ism.subset(pt_val, s);
        }

        void get_numerator(anum const & val, mpq & num) {
            scoped_mpq rat(m_am.qm());
            m_am.to_rational(val, rat);
            m_am.qm().get_numerator(rat, num);
        }

        void get_denominator(anum const & val, mpq & den) {
            scoped_mpq rat(m_am.qm());
            m_am.to_rational(val, rat);
            m_am.qm().get_denominator(rat, den);
        }

        bool lt_denominator(anum const & val1, anum const & val2) {
            scoped_mpq den1(m_am.qm());
            scoped_mpq den2(m_am.qm());
            get_denominator(val1, den1);
            get_denominator(val2, den2);
            return m_am.qm().lt(den1, den2);
        }

        bool is_simpler(anum const & val1, anum const & val2) {
            // Return whether val2 is simpler than val1
            if (m_am.is_rational(val1) && !m_am.is_rational(val2)) {
                return false;
            } else if (!m_am.is_rational(val1) && m_am.is_rational(val2)) {
                return true;
            } else if (!m_am.is_rational(val1) && !m_am.is_rational(val2)) {
                return false;  // cannot compare
            } else if (lt_denominator(val1, m_min) && lt_denominator(val2, m_min)) {
                return false;  // does not compare less than 10000
            } else {
                return lt_denominator(val2, val1);
            }
        }

        unsigned get_simplest_index(anum_vector & vs) {
            // Return the index in vs with "simplest" number. Ties are
            // broken by chance.
            vector<int> best_indices = vector<int>();
            best_indices.push_back(0);
            for (int i = 1; i < vs.size(); i++) {
                if (is_simpler(vs[best_indices[0]], vs[i])) {
                    best_indices.reset();
                    best_indices.push_back(i);
                } else if (!is_simpler(vs[i], vs[best_indices[0]])) {
                    best_indices.push_back(i);
                }
            }
            return best_indices[rand_int() % best_indices.size()];
        }

        void get_best_arith_value(var v, int best_score, anum & best_value, bool & from_eq, clause_index & eq_index) {
            // Obtain the best value for variable v (where the best score is known)
            SASSERT(best_score != INT_MIN);
            nra_arith_var * m_arith_var = m_arith_vars[v];
            int score = m_arith_var->m_start_score;
            int len = m_arith_var->m_boundaries.size();
            scoped_anum_vector vec(m_am);
            bool_vector values_eq;
            unsigned_vector clause_indices;
            if (score == best_score) {
                // Return value before left boundary
                if (m_arith_var->m_boundaries[0].is_open) {
                    // x] case, can include x
                    scoped_anum w(m_am);
                    m_am.set(w, m_arith_var->m_boundaries[0].value);
                    vec.push_back(w);
                    if(m_equal_clauses.contains(m_arith_var->m_boundaries[0].c_idx)) {
                        values_eq.push_back(true);
                        clause_indices.push_back(m_arith_var->m_boundaries[0].c_idx);
                    } else {
                        values_eq.push_back(false);
                        clause_indices.push_back(null_var);
                    }
                }
                else {
                    // x) case, cannot include x
                    scoped_anum w(m_am);
                    m_am.int_lt(m_arith_var->m_boundaries[0].value, w);
                    vec.push_back(w);
                    values_eq.push_back(false);
                    clause_indices.push_back(null_var);
                }
            }
            for (unsigned i = 0; i < len; i++) {
                score += m_arith_var->m_boundaries[i].score;
                if (score == best_score) {
                    // Return value after right boundary
                    if (i == len - 1) {
                        if (m_arith_var->m_boundaries[len-1].is_open) {
                            // x] case, cannot include x
                            scoped_anum w(m_am);
                            m_am.int_gt(m_arith_var->m_boundaries[len-1].value, w);
                            vec.push_back(w);
                            values_eq.push_back(false);
                            clause_indices.push_back(null_var);
                        }
                        else {
                            // x) case, can include x
                            scoped_anum w(m_am);
                            m_am.set(w, m_arith_var->m_boundaries[len-1].value);
                            vec.push_back(w);
                            if(m_equal_clauses.contains(m_arith_var->m_boundaries[len-1].c_idx)) {
                                values_eq.push_back(true);
                                clause_indices.push_back(m_arith_var->m_boundaries[len - 1].c_idx);
                            } else {
                                values_eq.push_back(false);
                                clause_indices.push_back(null_var);
                            }
                        }
                    }
                    // Return value in the middle
                    else {
                        if (m_am.eq(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value)) {
                            SASSERT(!m_arith_var->m_boundaries[i].is_open && m_arith_var->m_boundaries[i+1].is_open);
                            scoped_anum w(m_am);
                            m_am.set(w, m_arith_var->m_boundaries[i].value);
                            vec.push_back(w);
                            if(m_equal_clauses.contains(m_arith_var->m_boundaries[i].c_idx) || m_equal_clauses.contains(m_arith_var->m_boundaries[i+1].c_idx)) {
                                values_eq.push_back(true);
                                unsigned tmp = m_equal_clauses.contains(m_arith_var->m_boundaries[i].c_idx) ?
                                                m_arith_var->m_boundaries[i].c_idx : m_arith_var->m_boundaries[i+1].c_idx;
                                clause_indices.push_back(tmp);
                            } else {
                                values_eq.push_back(false);
                                clause_indices.push_back(null_var);
                            }
                        }
                        else {
                            scoped_anum w(m_am), w2(m_am);
                            // if (m_am.is_rational(m_arith_var->m_boundaries[i].value) &&
                            //     m_am.is_rational(m_arith_var->m_boundaries[i+1].value)) {
                            //     // Add (a + b) / 2
                            //     m_am.add(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value, w2);
                            //     m_am.div(w2, m_two, w);
                            //     vec.push_back(w);

                            //     // Add ratio of sum of numerator and denominator
                            //     scoped_mpq n1(m_am.qm());
                            //     scoped_mpq n2(m_am.qm());
                            //     scoped_mpq n3(m_am.qm());
                            //     scoped_mpq d1(m_am.qm());
                            //     scoped_mpq d2(m_am.qm());
                            //     scoped_mpq d3(m_am.qm());
                            //     scoped_mpq res(m_am.qm());
                            //     get_numerator(m_arith_var->m_boundaries[i].value, n1);
                            //     get_numerator(m_arith_var->m_boundaries[i+1].value, n2);
                            //     get_denominator(m_arith_var->m_boundaries[i].value, d1);
                            //     get_denominator(m_arith_var->m_boundaries[i].value, d2);
                            //     m_am.qm().add(n1, n2, n3);
                            //     m_am.qm().add(d1, d2, d3);
                            //     m_am.qm().div(n3, d3, res);
                            //     m_am.set(w, res);
                            //     vec.push_back(w);
                            // } else {
                                m_am.select(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value, w);
                                vec.push_back(w);
                                values_eq.push_back(false);
                                clause_indices.push_back(null_var);
                            // }
                        }
                    }
                }
            }
            SASSERT(vec.size() > 0);
            unsigned id = get_simplest_index(vec);
            SASSERT(id >= 0 && id < vec.size());
            m_am.set(best_value, vec[id]);
            from_eq = values_eq[id];
            eq_index = clause_indices[id];
            // best_value = vec[rand_int() % vec.size()];
            return;
        }

        bool get_best_arith_value_clause(var v, anum & best_value, clause_index c_idx, int & best_score, bool & from_eq, clause_index & eq_index) {
            // Obtain the best value for variable v, subject to the condition that
            // it is outside the infeasible interval of clause c_idx.
            nra_arith_var * m_arith_var = m_arith_vars[v];
            int score = m_arith_var->m_start_score;
            int len = m_arith_var->m_boundaries.size();
            scoped_anum_vector vec(m_am);
            vector<int> scores = vector<int>();
            bool_vector values_eq;
            unsigned_vector clause_indices;

            interval_set * s = nullptr;
            for (int i = 0; i < m_arith_var->m_clauses.size(); i++) {
                if (c_idx == m_arith_var->m_clauses[i]) {
                    s = m_arith_var->m_clause_intervals[i];
                }
            }
            if (m_ism.is_full(s)) {
                return false;
            }

            // Return value before left boundary
            if (m_arith_var->m_boundaries[0].is_open) {
                // x] case, can include x
                scoped_anum w(m_am);
                m_am.set(w, m_arith_var->m_boundaries[0].value);
                if (!contains_value(s, w) && score >= INT_MIN / 4) {
                    if (score > best_score) {
                        best_score = score;
                        scores.reset();
                        vec.reset();
                    }
                    scores.push_back(score);
                    vec.push_back(w);
                    clause_indices.push_back(m_arith_var->m_boundaries[0].c_idx);
                    if(m_equal_clauses.contains(m_arith_var->m_boundaries[0].c_idx)) {
                        values_eq.push_back(true);
                        clause_indices.push_back(m_arith_var->m_boundaries[0].c_idx);
                    } else {
                        values_eq.push_back(false);
                        clause_indices.push_back(null_var);
                    }
                }
            }
            else {
                // x) case, cannot include x
                scoped_anum w(m_am);
                m_am.int_lt(m_arith_var->m_boundaries[0].value, w);
                if (!contains_value(s, w) && score >= INT_MIN / 4) {
                    if (score > best_score) {
                        best_score = score;
                        scores.reset();
                        vec.reset();
                    }
                    scores.push_back(score);
                    vec.push_back(w);
                    values_eq.push_back(false);
                    clause_indices.push_back(null_var);
                }
            }

            for (unsigned i = 0; i < len; i++) {
                score += m_arith_var->m_boundaries[i].score;
                // Return value after right boundary
                if (i == len - 1) {
                    if (m_arith_var->m_boundaries[len-1].is_open) {
                        // x] case, cannot include x
                        scoped_anum w(m_am);
                        m_am.int_gt(m_arith_var->m_boundaries[len-1].value, w);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                            values_eq.push_back(false);
                            clause_indices.push_back(null_var);
                        }
                    }
                    else {
                        // x) case, can include x
                        scoped_anum w(m_am);
                        m_am.set(w, m_arith_var->m_boundaries[len-1].value);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                            if (m_equal_clauses.contains(m_arith_var->m_boundaries[len - 1].c_idx)) {
                                values_eq.push_back(true);
                                clause_indices.push_back(m_arith_var->m_boundaries[len - 1].c_idx);
                            } else {
                                values_eq.push_back(false);
                                clause_indices.push_back(null_var);
                            }
                        }
                    }
                }
                // Return value in the middle
                else {
                    if (m_am.eq(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value)) {
                        SASSERT(!m_arith_var->m_boundaries[i].is_open && m_arith_var->m_boundaries[i+1].is_open);
                        scoped_anum w(m_am);
                        m_am.set(w, m_arith_var->m_boundaries[i].value);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                            if (m_equal_clauses.contains(m_arith_var->m_boundaries[i].c_idx) || m_equal_clauses.contains(m_arith_var->m_boundaries[i + 1].c_idx)) {
                                values_eq.push_back(true);
                                unsigned tmp = m_equal_clauses.contains(m_arith_var->m_boundaries[i].c_idx) ? 
                                                m_arith_var->m_boundaries[i].c_idx : m_arith_var->m_boundaries[i+1].c_idx;
                                clause_indices.push_back(tmp);
                            } else {
                                values_eq.push_back(false);
                                clause_indices.push_back(null_var);
                            }
                        }
                    }
                    else {
                        scoped_anum w(m_am);
                        m_am.select(m_arith_var->m_boundaries[i].value, m_arith_var->m_boundaries[i+1].value, w);
                        if (!contains_value(s, w) && score >= INT_MIN / 4) {
                            if (score > best_score) {
                                best_score = score;
                                scores.reset();
                                vec.reset();
                            }
                            scores.push_back(score);
                            vec.push_back(w);
                            values_eq.push_back(false);
                            clause_indices.push_back(null_var);
                        }
                    }
                }
            }
            if (vec.size() == 0) {
                return false;
            }
            unsigned id = get_simplest_index(vec);
            SASSERT(id >= 0 && id < vec.size());
            m_am.set(best_value, vec[id]);
            best_score = scores[id];
            from_eq = values_eq[id];
            eq_index = clause_indices[id];
            // int r = rand_int() % vec.size();
            // best_value = vec[r];
            // best_score = scores[r];
            SASSERT(best_score >= INT_MIN / 4);
            return true;
        }

        int get_arith_score(var v, anum const & new_value) {
            // Obtain score from the index for updating variable v to new value
            nra_arith_var * m_arith_var = m_arith_vars[v];
            // std::cout << "query var " << v << " at value ";
            // m_am.display(std::cout, new_value);
            // std::cout << std::endl;
            int score;
            // score = m_arith_var->m_start_score;
            // std::cout << "start " << score << std::endl;
            // for (unsigned j = 0; j < m_arith_var->m_boundaries.size(); j++) {
            //     score += m_arith_var->m_boundaries[j].score;
            //     m_am.display(std::cout, m_arith_var->m_boundaries[j].value);
            //     std::cout << " " << m_arith_var->m_boundaries[j].is_open << " " << score << std::endl;
            // }
            score = m_arith_var->m_start_score;
            for (unsigned j = 0; j < m_arith_var->m_boundaries.size(); j++) {
                if (m_am.lt(new_value, m_arith_var->m_boundaries[j].value)) {
                    return score;
                }
                if (m_am.eq(new_value, m_arith_var->m_boundaries[j].value) && m_arith_var->m_boundaries[j].is_open) {
                    return score;
                }
                score += m_arith_var->m_boundaries[j].score;
            }
            return score;
        }

        void update_arith_score(var v, anum const & new_value) {
            // Update score in response to updating variable v to new value
            // We assume that satisfiability of clauses (and literals in it) has already
            // been updated. Loop over variables that share a clause with v.
            m_vars_visited.reset();
            nra_arith_var * m_arith_var = m_arith_vars[v];
            for (clause_index c_idx : m_arith_var->m_clauses) {
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                // Update for each variable in that clause
                for (auto it = curr_clause->m_vars.begin(); it != curr_clause->m_vars.end(); it++) {
                    var v2 = *it;
                    compute_arith_var_clause_info(v2, c_idx);
                }
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
        }

        void update_bool_score(bool_var b) {
            // Update score in response to flipping boolean variable
            m_vars_visited.reset();
            nra_bool_var * m_bool_var = m_bool_vars[b];
            for (clause_index c_idx : m_bool_var->m_clauses) {
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                // Update for each variable in that clause
                for (auto it = curr_clause->m_vars.begin(); it != curr_clause->m_vars.end(); it++) {
                    var v2 = *it;
                    compute_arith_var_clause_info(v2, c_idx);
                }
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
        }

        /**
         * Init Solution
         */
        // false means ICP returns unsat
        // only ICP for the first initialize
        bool init_solution(bool first_init){
            LSTRACE(tout << "start of init solution\n";);
            if(!construct_assignment(first_init)){
                return false;
            }
            init_literals_delta();
            init_clauses_delta();
            m_best_found_restart = m_num_clauses;
            update_solution_info();
            m_best_found_cost_bool = UINT_MAX;
            m_best_found_cost_nra = UINT_MAX;
            init_arith_var_info();
            LSTRACE(tout << "end of init solution\n";
                display_unsat_clauses(tout);
            );
            return true;
        }

        var find_unassigned_var(nra_clause const * cls) const {
            SASSERT(cls->get_left_vars() == 1);
            for(var v: cls->m_vars){
                if(m_assignment.is_assigned(v)){
                    continue;
                }
                return v;
            }
            return null_var;
        }

        var random_unassigned_var() {
            var res = null_var;
            unsigned curr = 1;
            for(var v = 0; v < m_num_vars; v++){
                if(m_assignment.is_assigned(v)){
                    continue;
                }
                // 1/curr
                if(rand_int() % curr == 0){
                    res = v;
                }
                curr++;
            }
            return res;
        }

        bool is_assigned_literal(nra_literal const * l) const {
            for(var v: l->m_vars){
                if(!m_assignment.is_assigned(v)){
                    return false;
                }
            }
            return true;
        }

        void update_unit_var_clauses(var x){
            for(clause_index i = 0; i < m_num_clauses; i++){
                nra_clause * cls = m_nra_clauses[i];
                cls->dec_left_vars(x);
                if(cls->get_left_vars() == 0 && m_unit_var_clauses.contains(i)){
                    m_unit_var_clauses.erase(i);
                }
                else if(cls->get_left_vars() == 1){
                    m_unit_var_clauses.insert_if_not_there(i);
                }
            }
        }

        // first init: ICP
        bool construct_assignment(bool first_init){
            return first_init ? init_assignment() : restart_assignment();
        }

        // ^ construct assignment for the first time
        bool init_assignment() {
            LSTRACE(tout << "start of init assignment\n";);
            m_assignment.reset();
            // bool vars set all true
            for(bool_var b = 0; b < m_num_bool_vars; b++){
                m_bool_vars[b]->set_value(true);
            }
            // arith vars set zero or other
            for(var v = 0; v < m_num_vars; v++){
                nra_arith_var const * curr_arith = m_arith_vars[v];
                // infeasible set full, ICP returns false
                if(m_ism.is_full(curr_arith->m_infeasible_st)){
                    return false;
                }
                LSTRACE(tout << "var " << v << ", "; m_ism.display(tout, curr_arith->m_feasible_st); tout << std::endl;);
                if(m_ism.contains_zero(curr_arith->m_feasible_st)){
                    LSTRACE(tout << "set zero\n";);
                    m_assignment.set(v, m_zero);
                }
                else {
                    LSTRACE(tout << "not zero\n";);
                    scoped_anum w(m_am);
                    m_ism.peek_in_complement(curr_arith->m_infeasible_st, false, w, true);
                    m_assignment.set(v, w);
                }
            }
            LSTRACE(tout << "end of init assignment\n";
                show_ls_assignment(tout);
            );
            return true;
        }

        // ^ construct assignment when restarting
        bool restart_assignment() {
            if(m_unsat_clauses.empty()){
                return true;
            }
            clause_index curr_index = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
            nra_clause const * curr_clause = m_nra_clauses[curr_index];
            SASSERT(curr_clause->size() > 0);
            literal_index l_idx = curr_clause->m_literals[rand_int() % curr_clause->size()];
            nra_literal const * curr_l = m_nra_literals[l_idx];
            if(curr_l->is_bool()){
                return true;
            }
            SASSERT(!curr_l->m_vars.empty());
            for(var v: curr_l->m_vars){
                if(m_var_value_fixed[v]){
                    continue;
                }
                nra_arith_var const * curr_arith = m_arith_vars[v];
                scoped_anum w(m_am), old_value(m_am);
                m_am.set(old_value, m_assignment.value(v));
                interval_set_ref old_value_interval(m_ism);
                // [old_value, old_value]
                old_value_interval = m_ism.mk_point_interval(old_value);
                interval_set_ref curr_st(m_ism);
                curr_st = m_ism.mk_union(old_value_interval, curr_arith->m_infeasible_st);
                // happens for ==
                if(m_ism.is_full(curr_st)){
                    m_var_value_fixed[v] = true;
                    continue;
                }
                m_ism.peek_in_complement(curr_st, false, w, true);
                m_assignment.set(v, w);
                return true;
            }
            return true;
        }

        void init_literals_delta(){
            LSTRACE(tout << "start of init literals delta\n";);
            for(literal_index i = 0; i < m_num_literals; i++){
                set_literal_anum(m_nra_literals[i]);
            }
            LSTRACE(tout << "end of init literals delta\n";);
        }

        void init_clauses_delta(){
            LSTRACE(tout << "start of init clauses delta\n";);
            m_num_unsat_literals = 0;
            m_num_bool_unsat_literals = 0;
            m_total_clause_weight = 0;

            m_sat_clause_with_false_literals.reset();
            m_unsat_clauses.reset();
            m_unsat_clauses_bool.reset();
            for(clause_index i = 0; i < m_num_clauses; i++){
                update_clause_delta(m_nra_clauses[i]);
            }
            m_total_clause_weight = m_num_clauses;
            LSTRACE(tout << "end of init clauses delta\n";
                display_unsat_clauses(tout);
            );
        }

        bool update_solution_info(){
            bool improved = false;
            if(m_unsat_clauses.size() < m_best_found_restart){
                improved = true;
                m_best_found_restart = m_unsat_clauses.size();
                m_best_cost_time = TimeElapsed();
            }
            return improved;
        }

        bool update_bool_info(){
            if(m_unsat_clauses.size() < m_best_found_cost_bool){
                m_best_found_cost_bool = m_unsat_clauses.size();
                return true;
            }
            return false;
        }

        bool update_nra_info(){
            if(m_unsat_clauses.size() < m_best_found_cost_nra){
                m_best_found_cost_nra = m_unsat_clauses.size();
                return true;
            }
            return false;
        }


        /**
         * Get Variables
         */
        void get_literal_vars(literal l, var_table & vars){
            vars.reset();
            if(is_bool_literal(l)){
                return;
            }
            ineq_atom * aa = to_ineq_atom(m_atoms[l.var()]);
            for(unsigned i = 0; i < aa->size(); i++){
                var_vector curr;
                poly * p = aa->p(i);
                m_pm.vars(p, curr);
                for(var v: curr){
                    if(!vars.contains(v)){
                        vars.insert(v);
                    }
                }
            }
        }

        /**
         * Set delta anum for literal
         */
        void set_literal_anum(nra_literal * l){
            // LSTRACE(tout << "start of set literal anum for "; m_solver.display(tout, l->m_literal); tout << std::endl;
            //     show_ls_assignment(tout);
            // );
            // std::cout << "start of set literal anum for "; m_solver.display(std::cout, l->m_literal); std::cout << std::endl;
            if(l->is_bool()){
                bool sat_status = is_bool_sat(l);
                l->set_sat_status(sat_status);
            }
            else {
                // we use evaluator's eval to check satisfiability of arith literals
                // checking sign of multi-poly is faster then getting accurate value
                l->set_sat_status(m_evaluator.eval((atom *) (l->get_atom()), l->sign()));
            }
            // LSTRACE(tout << "end of set literal anum\n";);
        }


        void update_clause_delta(nra_clause * cls){
            LSTRACE(tout << "start of update clause delta for: "; m_solver.display(tout, *cls->get_clause()); tout << std::endl;);
            unsigned sat_count = 0;
            literal_index last_sat = null_var;

            for(literal_index lit_index: cls->m_literals){
                nra_literal * curr_literal = m_nra_literals[lit_index];
                LSTRACE(tout << "loop literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;);
                if(curr_literal->get_sat_status()){
                    LSTRACE(tout << "sat literal\n";);
                    sat_count++;
                    last_sat = lit_index;
                }
            }
            cls->set_sat_count(sat_count);
            LSTRACE(tout << "sat count: " << sat_count << std::endl;);
            if(sat_count == 1){
                SASSERT(last_sat != null_var);
                cls->set_critical_index(last_sat);
            }
            else {
                cls->set_critical_index(null_var);
            }
            if(sat_count > 0){
                sat_clause(cls);
                LSTRACE(tout << "satisfy\n";);
                // false literal detected
                if(sat_count < cls->size()){
                    m_sat_clause_with_false_literals.insert(cls->get_index());
                }
            }
            else {
                unsat_clause(cls);
                LSTRACE(tout << "unsatisfy\n";);
                m_num_unsat_literals += cls->size();
                m_num_bool_unsat_literals += cls->bool_size();
                // bool variables in unsat clause increase score
                for(literal_index bool_lit_idx: cls->m_bool_literals){
                    nra_literal const * unsat_literal = m_nra_literals[bool_lit_idx];
                    LSTRACE(tout << "loop bool literal: "; m_solver.display(tout, unsat_literal->m_literal); tout << std::endl;);
                    SASSERT(unsat_literal->is_bool());
                    nra_bool_var * curr_bool = m_bool_vars[unsat_literal->get_bool_index()];
                    curr_bool->inc_score();
                }
            }
            // bool variable for sat count with 1 decrease score
            if(sat_count == 1){
                LSTRACE(tout << "sat count is 1, decrease critical literal's score\n";);
                // nra_literal const * critical_literal = m_nra_literals[min_index];
                nra_literal const * critical_literal = m_nra_literals[last_sat];
                SASSERT(critical_literal->get_sat_status());
                if(critical_literal->is_bool()){
                    SASSERT(critical_literal->get_bool_index() != null_var);
                    nra_bool_var * critical_bool = m_bool_vars[critical_literal->get_bool_index()];
                    critical_bool->dec_score();
                }
                else {
                    LSTRACE(tout << "critical literal is arith\n";);
                }
            }
            LSTRACE(display_clause_info(tout, cls););
            LSTRACE(tout << "end of update clause delta\n";);
        }

        /**
         * Sat
         */
        bool is_bool_sat(nra_literal const * l) const {
            SASSERT(l->is_bool());
            SASSERT(l->get_bool_index() != null_var);
            nra_bool_var * b = m_bool_vars[l->get_bool_index()];
            return l->sign() != b->get_value();
        }

        void set_const_anum(){
            m_am.set(m_zero, 0);
            m_am.set(m_one, 1);
            m_am.set(m_two, 2);
            m_am.set(m_ten, 10);
            // We primarily use m_min as a threshold for comparing denominators.
            // If two numbers have denominators smaller than that of m_min, they
            // are not distinguished in the comparison.
            scoped_anum threshold(m_am);
            m_am.set(threshold, 10);
            m_am.div(m_one, threshold, m_min);
            m_am.div(m_one, m_ten, m_slack_min);
            LSTRACE(display_const_anum(tout););
        }

        /**
         * Mode Switch
         */
        void enter_nra_mode(){
            is_bool_search = false;
            no_improve_cnt_nra = 0;
            m_best_found_cost_nra = m_unsat_clauses.size();
            LSTRACE(tout << "enter nra mode\n";);
        }

        void enter_bool_mode(){
            is_bool_search = true;
            no_improve_cnt_bool = 0;
            m_best_found_cost_bool = m_unsat_clauses.size();
            LSTRACE(tout << "enter bool mode\n";);
        }

        /**
         * Util
         */
        double TimeElapsed() {
            auto finish = std::chrono::steady_clock::now();
            std::chrono::duration<double> dura = finish - m_start_time;
            double res = dura.count();
            LSTRACE(tout << "Time Elapsed: " << res << std::endl;
                tout << "m_time_label: " << m_time_label << std::endl;
                std::cout << "elapsed: " << res << " s" << std::endl;
            );
            int curr_floor = floor(res);
            if(curr_floor >= m_time_label){
                // LSTRACE(std::cout << "Flow: " << curr_floor << " s" << std::endl;);
                m_time_label = curr_floor + 1;
            }
            return res;
        }

        var random_table(var_table const & vars) {
            if(vars.empty()){
                return null_var;
            }
            var res = null_var;
            unsigned count = 1;
            for(auto it = vars.begin(); it != vars.end(); it++){
                // 1/count to replace
                if(rand_int() % count == 0){
                    res = *it;
                }
                count++;
            }
            return res;
        }

        void get_common_vars(nra_literal const * l1, nra_literal const * l2, var_vector & vec) const {
            vec.reset();
            for(var v: l1->m_vars){
                if(l2->m_vars.contains(v)){
                    vec.push_back(v);
                }
            }
        }

        unsigned find_index_vector(var_vector const & vars, var v) const {
            for(unsigned i = 0; i < vars.size(); i++){
                if(vars[i] == v){
                    return i;
                }
            }
            return null_var;
        }

        void insert_in_complement(var v, interval_set const * s, literal_index l_idx){
            SASSERT(!m_ism.is_full(s));
            LSTRACE(
                tout << "insertion var " << v << std::endl;
                tout << "show set of insert: "; m_ism.display(tout, s); tout << std::endl;
            );
            anum_vector w_vec;
            m_ism.peek_in_complement_heuristic(s, w_vec);
            for(auto ele: w_vec){
                if(m_assignment.is_assigned(v) && m_am.eq(ele, m_assignment.value(v))){
                    continue;
                }
                if(m_nra_operation_table.contains(v, ele)){
                    continue;
                }
                m_nra_operation_index.push_back(v);
                m_nra_operation_value.push_back(ele);
                m_nra_operation_literal_index.push_back(l_idx);
            }
        }

        unsigned rand_int(){
            return m_rand();
        }

        void set_abs_anum(anum & res, anum const & w){
            m_am.set(res, w);
            if(m_am.is_neg(w)){
                m_am.neg(res);
            }
        }

        void sat_clause(nra_clause * cls){
            cls->set_sat_status(true);
            clause_index m_index = cls->get_index();
            m_unsat_clauses.erase(m_index);
            if(cls->bool_size() > 0){
                m_unsat_clauses_bool.erase(m_index);
            }
        }

        void unsat_clause(nra_clause * cls){
            cls->set_sat_status(false);
            clause_index m_index = cls->get_index();
            m_unsat_clauses.insert(m_index);
            if(cls->bool_size() > 0){
                m_unsat_clauses_bool.insert(m_index);
            }
            m_sat_clause_with_false_literals.erase(m_index);
            // m_num_unsat_literals += cls->size();
            // m_num_bool_unsat_literals += cls->bool_size();
        }

        bool is_bool_literal(literal l) const {
            return m_atoms[l.var()] == nullptr;
        }

        bool is_arith_literal(literal l) const {
            return !is_bool_literal(l);
        }

        unsigned find_literal_vector(literal_vector const & vec, literal l) const {
            for(unsigned i = 0; i < vec.size(); i++){
                if(vec[i] == l){
                    return i;
                }
            }
            return UINT_MAX;
        }

        void collect_bool_values(){
            for(bool_var b = 0; b < m_bool_vars.size(); b++){
                m_bvalues[m_bool_vars[b]->get_origin_index()] = b2lb(m_bool_vars[b]->get_value());
            }
        }

        static lbool b2lb(bool b) {
            return b ? l_true : l_false;
        }

        bool_var select_best_from_bool_operations(int & best_score){
            // set BMS and cnt
            unsigned cnt = m_bool_operation_index.size();
            unsigned best_last_move = UINT_MAX;
            bool_var m_curr_operation, best_bool_var_index = null_var;
            // loop bool operations
            for(unsigned i = 0; i < cnt; i++){
                m_curr_operation = m_bool_operation_index[i];
                nra_bool_var const * curr_bool = m_bool_vars[m_curr_operation];
                int score = get_bool_critical_score(m_curr_operation);
                if(score > best_score || (score == best_score && curr_bool->get_last_move() < best_last_move)){
                    best_score = score;
                    best_last_move = curr_bool->get_last_move();
                    best_bool_var_index = m_curr_operation;
                }
            }
            return best_bool_var_index;
        }

        /**
         * * Critical Move
         */
        int pick_critical_move(bool_var & bvar, var & avar, anum & best_value, int & best_score, bool & from_eq, clause_index & equal_index){
            LSTRACE(tout << "show time of start picking move\n";
                TimeElapsed();
            );
            LSTRACE(tout << "start of pick move\n";
                show_ls_assignment(tout);
            );
            m_bool_operation_index.reset();
            reset_arith_operation();
            SASSERT(!m_unsat_clauses.empty());

            if (is_random_walk) {
                // Random walk case
                clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];

                m_vars_visited.reset();

                vector<var> best_arith_index = vector<var>();
                scoped_anum_vector arith_vals(m_am);
                vector<int> best_scores = vector<int>();
                bool_vector sample_from_equations;
                unsigned_vector sample_equal_indices;
                for (literal_index l_idx : curr_clause->m_arith_literals) {
                    nra_literal const * curr_literal = m_nra_literals[l_idx];
                    for (var v : curr_literal->m_vars) {
                        if (!m_vars_visited.contains(v)) {
                            m_vars_visited.insert(v);
                            scoped_anum best_value(m_am);
                            int best_score = INT_MIN;
                            bool from_eq;
                            clause_index eq_index = null_var;
                            if (get_best_arith_value_clause(v, best_value, c_idx, best_score, from_eq, eq_index)) {
                                best_arith_index.push_back(v);
                                arith_vals.push_back(best_value);
                                best_scores.push_back(best_score);
                                sample_from_equations.push_back(from_eq);
                                sample_equal_indices.push_back(eq_index);
                            }
                        }
                    }
                }

                vector<bool_var> best_bool_index = vector<bool_var>();
                for (literal_index l_idx : curr_clause->m_bool_literals) {
                    nra_literal const * curr_literal = m_nra_literals[l_idx];
                    SASSERT(curr_literal->is_bool());
                    bool_var b = curr_literal->get_bool_index();
                    best_bool_index.push_back(b);
                }
                int total_size = best_bool_index.size() + best_arith_index.size();
                if (total_size > 0) {
                    int r = rand_int() % total_size;
                    if (r < best_bool_index.size()) {
                        bvar = best_bool_index[r];
                        best_score = get_bool_critical_score(bvar);
                        from_eq = false;
                        equal_index = null_var;
                        return 0;  // bool operation
                    } else {
                        SASSERT(arith_vals.size() > 0);
                        unsigned id = get_simplest_index(arith_vals);
                        avar = best_arith_index[id];
                        m_am.set(best_value, arith_vals[id]);
                        best_score = best_scores[id];
                        from_eq = sample_from_equations[id];
                        // avar = best_arith_index[r - best_bool_index.size()];
                        // best_value = arith_vals[r - best_bool_index.size()];
                        // best_score = best_scores[r - best_bool_index.size()];
                        equal_index = sample_equal_indices[id];
                        if (!is_simpler(best_value, m_min)) {
                            return 1;  // arith operation
                        }
                    }
                }
            } else {
                // Greedy case
                int curr_score;
                int best_arith_score = INT_MIN;
                vector<var> best_arith_index = vector<var>();
                scoped_anum_vector best_values(m_am);
                for (var v = 0; v < m_arith_vars.size(); v++) {
                    curr_score = get_best_arith_score(v);
                    if (curr_score > best_arith_score) {
                        best_arith_score = curr_score;
                    }
                }
                bool_vector best_from_equations;
                unsigned_vector sample_equal_indices;
                if (best_arith_score != INT_MIN) {
                    for (var v = 0; v < m_arith_vars.size(); v++) {
                        curr_score = get_best_arith_score(v);
                        if (curr_score == best_arith_score) {
                            best_arith_index.push_back(v);
                            scoped_anum w(m_am);
                            bool from_eq;
                            clause_index eq_index = null_var;
                            get_best_arith_value(v, curr_score, w, from_eq, eq_index);
                            best_values.push_back(w);
                            best_from_equations.push_back(from_eq);
                            sample_equal_indices.push_back(eq_index);
                        }
                    }
                }

                int best_bool_score = INT_MIN;
                vector<bool_var> best_bool_index = vector<bool_var>();
                for (bool_var b = 0; b < m_bool_vars.size(); b++) {
                    curr_score = get_bool_critical_score(b);
                    if (curr_score > best_bool_score) {
                        best_bool_score = curr_score;
                        best_bool_index.reset();
                        best_bool_index.push_back(b);
                    } else if (curr_score == best_bool_score) {
                        best_bool_index.push_back(b);
                    }
                }

                if (best_bool_score > 0 || best_arith_score > 0) {
                    // Has decreasing move
                    if (best_bool_score > best_arith_score) {
                        bvar = best_bool_index[rand_int() % best_bool_index.size()];
                        best_score = best_bool_score;
                        from_eq = false;
                        equal_index = null_var;
                        return 0;  // bool operation
                    }
                    else if (best_bool_score < best_arith_score) {
                        SASSERT(best_values.size() > 0);
                        unsigned id = get_simplest_index(best_values);
                        SASSERT(id >= 0 && id < best_values.size());
                        avar = best_arith_index[id];
                        best_score = best_arith_score;
                        from_eq = best_from_equations[id];
                        m_am.set(best_value, best_values[id]);
                        equal_index = sample_equal_indices[id];
                        // avar = best_arith_index[rand_int() % best_arith_index.size()];
                        // get_best_arith_value(avar, best_arith_score, best_value);
                        return 1;  // arith operation
                    } else {
                        int total_size = best_bool_index.size() + best_arith_index.size();
                        int r = rand_int() % total_size;
                        if (r < best_bool_index.size()) {
                            bvar = best_bool_index[r];
                            best_score = best_bool_score;
                            from_eq = false;
                            return 0;  // bool operation
                        } else {
                            SASSERT(best_values.size() > 0);
                            unsigned id = get_simplest_index(best_values);
                            SASSERT(id >= 0 && id < best_values.size());
                            avar = best_arith_index[id];
                            best_score = best_arith_score;
                            m_am.set(best_value, best_values[id]);
                            from_eq = best_from_equations[id];
                            equal_index = sample_equal_indices[id];
                            // avar = best_arith_index[r - best_bool_index.size()];
                            // best_score = best_arith_score;
                            // get_best_arith_value(avar, best_arith_score, best_value);
                            return 1;  // arith operation
                        }
                    }
                }

                // update clause weight
                if(rand_int() % 500 > smooth_probability){
                    update_clause_weight();
                }
                else {
                    smooth_clause_weight();
                }
                no_operation_random_walk();
            }

            LSTRACE(tout << "end of pick move\n";);
            LSTRACE(tout << "show time of end picking move\n";
                TimeElapsed();
            );
            return -1;  // no operation found
        }

        void reset_chosen_bool(){
            for(bool_var idx: m_bool_operation_index){
                m_bool_is_chosen[idx] = false;
            }
        }

        var select_best_from_arith_operations(int & best_score, anum & best_value, literal_index & best_literal_index){
            unsigned cnt = m_nra_operation_index.size();
            var m_arith_index;
            scoped_anum m_arith_value(m_am);
            literal_index m_literal_index;
            unsigned best_last_move = UINT_MAX, best_arith_index = null_var;
            best_literal_index = null_var;
            for(unsigned i = 0; i < cnt; i++){
                m_arith_index = m_nra_operation_index[i];
                m_literal_index = m_nra_operation_literal_index[i];
                m_am.set(m_arith_value, m_nra_operation_value[i]);

                // int curr_score = get_arith_critical_score(m_arith_index, m_arith_value);
                int curr_score = get_arith_score(m_arith_index, m_arith_value);
                // if (curr_score != curr_score2) {
                //     std::cout << "Error: " << curr_score << " vs " << curr_score2 << std::endl;
                //     exit(0);
                // } else {
                //     // std::cout << "Correct: " << curr_score << std::endl;
                // }
                nra_arith_var const * curr_arith = m_arith_vars[m_arith_index];
                // compare arith score and last move
                if(curr_score > best_score || (curr_score == best_score && curr_arith->get_last_move() < best_last_move)){
                    best_score = curr_score;
                    best_last_move = curr_arith->get_last_move();
                    best_arith_index = m_arith_index;
                    m_am.set(best_value, m_arith_value);
                    best_literal_index = m_literal_index;
                }
            }
            return best_arith_index;
        }

        void add_literal_arith_operation(nra_literal const * l){
            LSTRACE(tout << "add operation for literal\n";
                m_solver.display(tout, l->m_literal); tout << std::endl;
            );
            SASSERT(l->is_arith());
            if(m_literal_added.contains(l->get_index())){
                return;
            }
            m_literal_added.insert(l->get_index());
            for(var v: l->m_vars){
                nra_arith_var const * curr_arith = m_arith_vars[v];
                if(m_step <= curr_arith->get_tabu()){
                    continue;
                }
                interval_set_ref curr_st(m_ism);
                curr_st = m_evaluator.infeasible_intervals(l->get_atom(), l->sign(), nullptr, v);
                if(m_ism.is_full(curr_st)){
                    continue;
                }
                interval_set_ref union_st(m_ism);
                union_st = m_ism.mk_union(curr_st, curr_arith->m_infeasible_st);
                if(m_ism.is_full(union_st)){
                    continue;
                }
                insert_in_complement(v, union_st, l->get_index());
            }
        }

        // pick var with coeff !=0, move to zero
        poly * get_atom_polys(ineq_atom const * a) const {
            LSTRACE(tout << "size: " << a->size() << std::endl;);
            SASSERT(a->size() > 0);
            poly * p = a->p(0);
            for(unsigned i = 1; i < a->size(); i++){
                poly * curr = a->p(i);
                p = m_pm.mul(p, curr);
            }
            return p;
            // return nullptr;
        }

        // get variables in unsat unit clauses
        void get_unsat_unit_vars(var_table & vec){
            vec.reset();
            for(clause_index cls_idx: m_unsat_clauses){
                if(m_unit_clauses.contains(cls_idx)){
                    nra_clause const * cls = m_nra_clauses[cls_idx];
                    for(var v: cls->m_vars){
                        if(!vec.contains(v)){
                            vec.insert(v);
                        }
                    }
                }
            }
        }

        void reset_arith_operation(){
            m_nra_operation_index.reset();
            m_nra_operation_value.reset();
            m_nra_operation_literal_index.reset();
            m_literal_added.reset();
        }

        /**
         * Score
         */
        // get score for critical nra move
        int get_arith_critical_score(var v, anum const & new_value){
            LSTRACE(tout << "start of get arith critical score\n";
                TimeElapsed();
            );
            int res_score = 0;
            // store old assignment
            scoped_anum old_value(m_am);
            m_am.set(old_value, m_assignment.value(v));
            LSTRACE(tout << "var: " << v << std::endl;
                tout << "value: "; m_am.display(tout, old_value); tout << "->"; 
                m_am.display(tout, new_value);
                tout << std::endl;
            );
            nra_arith_var const * m_arith_var = m_arith_vars[v];
            // assign new value
            m_assignment.set(v, new_value);
            // loop all literal-clause pairs in this arith variable
            // literal 0 1 3 4 1 ...
            // clause  0 0 1 1 1 ...
            SASSERT(m_arith_var->m_literals.size() == m_arith_var->m_lit_cls.size());
            int make_break = 0; 

            m_literal_index_visited.reset();
            m_literal_before_sat.reset();
            for(unsigned i = 0; i < m_arith_var->m_literals.size(); i++){
                literal_index l_idx = m_arith_var->m_literals[i];
                clause_index c_idx = m_arith_var->m_lit_cls[i];
                nra_literal * curr_literal = m_nra_literals[l_idx];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                LSTRACE(
                    tout << "consider literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;
                    tout << "consider clause: "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;
                );
                SASSERT(curr_literal->is_arith());
                unsigned find_result = find_index_vector(m_literal_index_visited, l_idx);
                bool before_sat, after_sat;
                // not found
                if(find_result == null_var){
                    before_sat = curr_literal->get_sat_status();
                    set_literal_anum(curr_literal);
                    after_sat = curr_literal->get_sat_status();
                    m_literal_index_visited.push_back(l_idx);
                    m_literal_before_sat.push_back(before_sat);
                }
                // found
                else {
                    before_sat = m_literal_before_sat[find_result];
                    after_sat = curr_literal->get_sat_status();
                }
                make_break += (after_sat - before_sat);
                LSTRACE(
                    tout << "bool value: "; tout << (before_sat ? "true" : "false"); tout << "->"; tout << (after_sat ? "true" : "false"); tout << std::endl;
                );

                // the end of a clause block (claus block means an area of the same clause index)
                // time to count clause count
                if(i == m_arith_var->m_literals.size() - 1 || (c_idx != m_arith_var->m_lit_cls[i + 1])){
                    LSTRACE(tout << "end for clause "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                    unsigned before_sat_count = curr_clause->get_sat_count();
                    LSTRACE(tout << "show make break: " << make_break << std::endl;);
                    unsigned after_sat_count = before_sat_count + make_break;
                    LSTRACE(tout << "sat count in get score: " << before_sat_count << "->" << after_sat_count << std::endl;);
                    SASSERT(after_sat_count >= 0);
                    // unsat --> sat
                    if(before_sat_count == 0 && after_sat_count > 0){
                        // std::cout << "make clause " << c_idx << " literal " << l_idx << " weight " << curr_clause->get_weight() << std::endl;
                        res_score += curr_clause->get_weight();
                    }
                    // sat --> unsat
                    else if(before_sat_count > 0 && after_sat_count == 0){
                        // std::cout << "break clause " << c_idx << " literal " << l_idx << " weight " << curr_clause->get_weight() << std::endl;
                        res_score -= curr_clause->get_weight();
                    }
                    make_break = 0;
                }
            }
            // restore assignment
            m_assignment.set(v, old_value);
            restore_literal_info();
            LSTRACE(tout << "end of get arith critical score, score: " << res_score << std::endl;
                TimeElapsed();
            );
            return res_score;
        }

        // get score for critical bool move
        int get_bool_critical_score(var b){
            int res_score = 0;
            nra_bool_var * m_bool_var = m_bool_vars[b];

            // loop all literal-clause pairs in this arith variable
            // literal 0 1 3 4 1 ...
            // clause  0 0 1 1 1 ...
            SASSERT(m_bool_var->m_literals.size() == m_bool_var->m_lit_cls.size());
            int make_break = 0; 

            for(unsigned i = 0; i < m_bool_var->m_literals.size(); i++){
                literal_index l_idx = m_bool_var->m_literals[i];
                clause_index c_idx = m_bool_var->m_lit_cls[i];
                nra_literal * curr_literal = m_nra_literals[l_idx];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                LSTRACE(
                    tout << "consider literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;
                    tout << "consider clause: "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;
                );
                SASSERT(curr_literal->is_bool());
                bool before_sat, after_sat;
                before_sat = is_literal_sat(curr_literal);
                after_sat = !before_sat;
                make_break += (after_sat - before_sat);
                LSTRACE(
                    tout << "bool value: "; tout << (before_sat ? "true" : "false"); tout << "->"; tout << (after_sat ? "true" : "false"); tout << std::endl;
                );

                // the end of a clause block (claus block means an area of the same clause index)
                // time to count clause count
                if(i == m_bool_var->m_literals.size() - 1 || (c_idx != m_bool_var->m_lit_cls[i + 1])){
                    LSTRACE(tout << "end for clause "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                    unsigned before_sat_count = curr_clause->get_sat_count();
                    LSTRACE(tout << "show make break: " << make_break << std::endl;);
                    unsigned after_sat_count = before_sat_count + make_break;
                    LSTRACE(tout << "sat count in get score: " << before_sat_count << "->" << after_sat_count << std::endl;);
                    SASSERT(after_sat_count >= 0);
                    // unsat --> sat
                    if(before_sat_count == 0 && after_sat_count > 0){
                        res_score += curr_clause->get_weight();
                    }
                    // sat --> unsat
                    else if(before_sat_count > 0 && after_sat_count == 0){
                        res_score -= curr_clause->get_weight();
                    }
                    make_break = 0;
                }
            }
            return res_score;
        }
        
        void restore_literal_info(){
            for(unsigned i = 0; i < m_literal_index_visited.size(); i++){
                literal_index l_idx = m_literal_index_visited[i];
                bool before_sat = m_literal_before_sat[i];
                nra_literal * curr_literal = m_nra_literals[l_idx];
                curr_literal->set_sat_status(before_sat);
            }
        }

        /**
         * Critical Move
         */
        void critical_bool_move(bool_var b){
            LSTRACE(tout << "start of critical bool move\n";);
            LSTRACE(tout << "show time entering critical bool move\n";
                TimeElapsed();
            );
            nra_bool_var * b_var = m_bool_vars[b];
            int origin_score = b_var->get_score();
            critical_subscore_bool(b);
            // flip the bool variable
            b_var->set_value(!b_var->get_value());
            // update bool score
            update_bool_score(b);
            b_var->set_score(b_var->get_score() - origin_score);
            // update step
            b_var->set_last_move(m_outer_step);
            b_var->set_tabu(m_outer_step + 1 + rand_int() % 3);
            m_outer_step++;
            LSTRACE(tout << "end of critical bool move\n";);
            LSTRACE(tout << "show time exiting critical bool move\n";
                TimeElapsed();
            );
        }

        // has not been flipped yet
        void critical_subscore_bool(bool_var b){
            // has not been assigned
            nra_bool_var * b_var = m_bool_vars[b];
            LSTRACE(tout << "start of critical subscore bool for bool var: " << b << std::endl;);
            int make_break = 0;
            m_literal_index_visited.reset();
            // same literal may appear, because same literals can be found in different clauses
            // in this case, we update literal's sat status at last
            
            for(unsigned i = 0; i < b_var->m_literals.size(); i++){
                literal_index l_idx = b_var->m_literals[i];
                if(!m_literal_index_visited.contains(l_idx)){
                    m_literal_index_visited.push_back(l_idx);
                }
                nra_literal * curr_literal = m_nra_literals[l_idx];
                bool before_sat = curr_literal->get_sat_status();
                LSTRACE(tout << "consider literal "; 
                    m_solver.display(tout, curr_literal->m_literal); tout << std::endl;
                );
                // true --> false
                if(before_sat){
                    LSTRACE(tout << "true --> false\n";);
                    make_break = -1;
                }
                // false --> true
                else {
                    LSTRACE(tout << "false --> true\n";);
                    make_break = 1;
                }
                // we assume that for a bool variable, 
                // it won't appear in the same clause twice or more
                clause_index c_idx = b_var->m_lit_cls[i];
                nra_clause * curr_clause = m_nra_clauses[c_idx];
                unsigned before_sat_count = curr_clause->get_sat_count();
                literal_index before_critical_literal = null_var;
                if(before_sat_count == 1){
                    before_critical_literal = curr_clause->get_critical_index();
                    SASSERT(before_critical_literal != null_var);
                }
                unsigned after_sat_count = before_sat_count + make_break;
                curr_clause->set_sat_count(after_sat_count);
                LSTRACE(tout << "show clause:\n";
                    m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;
                    tout << "before sat count: " << before_sat_count << std::endl;
                    show_ls_assignment(tout);
                );

                // set critical literal index
                if(after_sat_count == 1){
                    SASSERT(before_sat_count == 2 || before_sat_count == 0);
                    // 2 --> 1
                    // critical index must be sat literals except critical moved one
                    if(before_sat_count == 2){
                        curr_clause->set_critical_index(find_sat_literal_except(curr_clause, l_idx));
                    } 
                    // 0 --> 1
                    // critical index must be critical moved one
                    else if(before_sat_count == 0){
                        curr_clause->set_critical_index(l_idx);
                    } 
                    else {
                        UNREACHABLE();
                    }
                }
                else {
                    curr_clause->set_critical_index(null_var);
                }

                // sat --> unsat
                if(before_sat > 0 && after_sat_count == 0){
                    unsat_clause(curr_clause);
                    m_num_unsat_literals += curr_clause->size();
                    m_num_bool_unsat_literals += curr_clause->bool_size();
                }
                // unsat --> sat
                else if(before_sat == 0 && after_sat_count > 0){
                    sat_clause(curr_clause);
                    m_num_unsat_literals -= curr_clause->size();
                    m_num_bool_unsat_literals -= curr_clause->bool_size();
                }
                // sat clause with false literals
                if(after_sat_count > 0 && after_sat_count < curr_clause->size()){
                    m_sat_clause_with_false_literals.insert(c_idx);
                }
                else {
                    m_sat_clause_with_false_literals.erase(c_idx);
                }
                // update bool variable score
                if(make_break > 0){
                    // unsat --> sat
                    // bool literal decrease score
                    if(before_sat_count == 0){
                        for(literal_index loop_idx: curr_clause->m_bool_literals){
                            nra_literal const * loop_literal = m_nra_literals[loop_idx];
                            nra_bool_var * loop_bvar = m_bool_vars[loop_literal->get_bool_index()];
                            loop_bvar->set_score(loop_bvar->get_score() - curr_clause->get_weight());
                        }
                    }
                    // sat number: 1 --> x > 1
                    // befre critical literal increase score
                    else if(before_sat_count == 1){
                        nra_literal const * min_literal = m_nra_literals[before_critical_literal];
                        if(min_literal->is_bool()){
                            nra_bool_var * min_bvar = m_bool_vars[min_literal->get_bool_index()];
                            min_bvar->set_score(min_bvar->get_score() + curr_clause->get_weight());
                        }
                    }
                }
                else if(make_break < 0){
                    // sat == 1 --> unsat
                    // all bool literal increase score
                    if(after_sat_count == 0){
                        for(literal_index loop_idx: curr_clause->m_bool_literals){
                            nra_literal const * loop_literal = m_nra_literals[loop_idx];
                            nra_bool_var * loop_bvar = m_bool_vars[loop_literal->get_bool_index()];
                            loop_bvar->set_score(loop_bvar->get_score() + curr_clause->get_weight());
                        }
                    }
                    // 2 --> 1
                    // curr critical literal increase score
                    else if(after_sat_count == 1){
                        literal_index curr_critical =  curr_clause->get_critical_index();
                        nra_literal const * min_literal = m_nra_literals[curr_critical];
                        if(min_literal->is_bool()){
                            nra_bool_var * min_bvar = m_bool_vars[min_literal->get_bool_index()];
                            min_bvar->set_score(min_bvar->get_score() - curr_clause->get_weight());
                        }
                    }
                }
            }
            for(literal_index l_idx: m_literal_index_visited){
                nra_literal * curr_l = m_nra_literals[l_idx];
                curr_l->flip_sat_status();
            }
            LSTRACE(tout << "end of critical subscore bool\n";);
        }

        void critical_nra_move(var v, anum const & value){
            scoped_anum old_value(m_am);
            m_am.set(old_value, m_assignment.value(v));
            LSTRACE(tout << "start of critical nra move\n";
                tout << "var: " << v << std::endl;
                tout << "value: "; m_am.display(tout, old_value);
                tout << "->";
                m_am.display(tout, value); tout << std::endl;
                display_unsat_clauses(tout);
            );
            LSTRACE(show_ls_assignment(tout););
            m_assignment.set(v, value);

            // std::cout << "var: " << v << std::endl;
            // std::cout << "value: "; m_am.display(std::cout, old_value);
            // std::cout << "->";
            // m_am.display(std::cout, value); std::cout << std::endl;

            critical_subscore_nra(v, value);
            // update arith score, except when the problem is already solved
            if (m_unsat_clauses.size() > 0) {
                update_arith_score(v, value);
            }
            nra_arith_var * v_var = m_arith_vars[v];
            v_var->set_last_move(m_step);
            v_var->set_tabu(m_step + 3 + rand_int() % 10);
            LSTRACE(tout << "end of critical nra move\n";
                display_unsat_clauses(tout);
            );
        }

        literal_index find_sat_literal(nra_clause const * cls) const {
            for(literal_index l: cls->m_literals){
                nra_literal const * lit = m_nra_literals[l];
                if(lit->get_sat_status()){
                    return l;
                }
            }
            UNREACHABLE();
            return null_var;
        }

        literal_index find_sat_literal_except(nra_clause const * cls, literal_index idx) const {
            SASSERT(m_nra_literals[idx]->get_sat_status());
            for(literal_index l_idx: cls->m_literals){
                if(l_idx == idx){
                    continue;
                }
                nra_literal const * lit = m_nra_literals[l_idx];
                if(lit->get_sat_status()){
                    return l_idx;
                }
            }
            UNREACHABLE();
            return null_var;
        }

        void critical_subscore_nra(var v, anum const & value){
            LSTRACE(tout << "start of nra subscore\n";
                tout << "var: " << v << std::endl;
                tout << "value: "; m_am.display(tout, value); tout << std::endl;
                show_ls_assignment(tout);
            );
            LSTRACE(tout << "show time entering critical nra move\n";
                TimeElapsed();
            );
            // has been assigned
            nra_arith_var * v_var = m_arith_vars[v];
            int make_break = 0;
            var_vector m_literal_occured;
            // check whether has been changed anum and sat_status
            m_literal_index_visited.reset();
            m_literal_before_sat.reset();
            // if a literal has been reset literal, its before anum and before sat has also been changed

            for(unsigned i = 0; i < v_var->m_literals.size(); i++){
                literal_index l_idx = v_var->m_literals[i];
                m_literal_occured.push_back(l_idx);
                nra_literal * curr_literal = m_nra_literals[l_idx];
                clause_index c_idx = v_var->m_lit_cls[i];
                nra_clause * curr_clause = m_nra_clauses[c_idx];
                literal_index before_critical_index = null_var;
                if(curr_clause->get_sat_count() == 1){
                    before_critical_index = curr_clause->get_critical_index();
                }
                LSTRACE(tout << "consider literal: "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;);
                bool before_sat, after_sat;
                // not found
                unsigned find_result = find_index_vector(m_literal_index_visited, l_idx);
                if(find_result == null_var){
                    before_sat = curr_literal->get_sat_status();
                    LSTRACE(tout << "not cached literal\n";);
                    set_literal_anum(curr_literal);
                    after_sat = curr_literal->get_sat_status();
                    // insert literal
                    m_literal_index_visited.push_back(l_idx);
                    m_literal_before_sat.push_back(before_sat);
                    SASSERT(m_literal_index_visited.size() == m_literal_before_sat.size());
                }
                // found cached
                else {
                    LSTRACE(tout << "cached literal\n";
                        display_literal_vector(tout, m_literal_index_visited);
                        display_bool_vector(tout, m_literal_before_sat);
                        tout << "find result: " << find_result << std::endl;
                    );
                    before_sat = m_literal_before_sat[find_result];
                    after_sat = curr_literal->get_sat_status();
                }
                make_break += (after_sat - before_sat);
                LSTRACE(
                    tout << "critical move bool value: "; tout << (before_sat ? "true" : "false"); tout << "->"; tout << (after_sat ? "true" : "false"); tout << std::endl;
                );
                // update delta informatiom
                // the end of a clause block (claus block means an area of the same clause index)
                // time to count clause count
                if(i == v_var->m_literals.size() - 1 || c_idx != v_var->m_lit_cls[i + 1]){
                    LSTRACE(tout << "enter new clause in critical nra move\n";);
                    unsigned before_sat_count = curr_clause->get_sat_count();
                    unsigned after_sat_count = before_sat_count + make_break;
                    curr_clause->set_sat_count(after_sat_count);
                    LSTRACE(tout << "consider clause: "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                    LSTRACE(
                        tout << "make break: " << make_break << std::endl;
                        tout << "critical sat count: " << before_sat_count << "->" << after_sat_count << std::endl;);
                    // sat --> unsat
                    if(before_sat_count > 0 && after_sat_count == 0){
                        unsat_clause(curr_clause);
                        m_num_unsat_literals += curr_clause->size();
                        m_num_bool_unsat_literals += curr_clause->bool_size();
                    }
                    // unsat --> sat
                    else if(before_sat_count == 0 && after_sat_count > 0){
                        sat_clause(curr_clause);
                        m_num_unsat_literals -= curr_clause->size();
                        m_num_bool_unsat_literals -= curr_clause->bool_size();
                    }

                    // critical index
                    if(after_sat_count == 1){
                        curr_clause->set_critical_index(find_sat_literal(curr_clause));
                    }
                    else {
                        curr_clause->set_critical_index(null_var);
                    }

                    // we update bool variable's score
                    if(make_break > 0){
                        // unsat --> sat
                        // all bool variable decrease score
                        if(before_sat_count == 0){
                            for(literal_index loop_idx: curr_clause->m_bool_literals){
                                nra_literal const * bool_literal = m_nra_literals[loop_idx];
                                nra_bool_var * curr_bool = m_bool_vars[bool_literal->get_bool_index()];
                                curr_bool->set_score(curr_bool->get_score() - curr_clause->get_weight());
                            }
                        }
                        // sat number: 1 --> x > 1
                        // before bool critical literal increase score
                        else if(before_sat_count == 1){
                            nra_literal const * min_index_literal = m_nra_literals[before_critical_index];
                            if(min_index_literal->is_bool()){
                                nra_bool_var * curr_bool = m_bool_vars[min_index_literal->get_bool_index()];
                                curr_bool->set_score(curr_bool->get_score() + curr_clause->get_weight());
                            }
                        }
                    }
                    else if(make_break < 0){
                        // sat --> unsat
                        // all bool variable increase score
                        if(after_sat_count == 0){
                            for(literal_index loop_idx: curr_clause->m_bool_literals){
                                nra_literal const * bool_literal = m_nra_literals[loop_idx];
                                nra_bool_var * curr_bool = m_bool_vars[bool_literal->get_bool_index()];
                                curr_bool->set_score(curr_bool->get_score() + curr_clause->get_weight());
                            }
                        }
                        // critical bool variable decrease score
                        else if(after_sat_count == 1){
                            literal_index min_index = curr_clause->get_critical_index();
                            SASSERT(min_index != null_var);
                            nra_literal const * min_index_literal = m_nra_literals[min_index];
                            if(min_index_literal->is_bool()){
                                nra_bool_var * curr_bool = m_bool_vars[min_index_literal->get_bool_index()];
                                curr_bool->set_score(curr_bool->get_score() - curr_clause->get_weight());
                            }
                        }
                    }
                    // restore make break and new_future
                    make_break = 0;
                    m_literal_occured.reset();
                }
            }
            LSTRACE(tout << "end of nra subscore\n";);
            LSTRACE(tout << "show time exiting nra subscore\n";
                TimeElapsed();
            );
        }

        /**
         * Weight
         */
        void update_clause_weight(){
            // update unsat clauses weight
            m_vars_visited.reset();
            for(clause_index idx: m_unsat_clauses){
                nra_clause * cls = m_nra_clauses[idx];
                cls->inc_weight();
                // increase bool score for unsat clauses (because we increase weight for clause)
                for(literal_index lit_idx: cls->m_bool_literals){
                    nra_literal const * curr_literal = m_nra_literals[lit_idx];
                    nra_bool_var * curr_bool = m_bool_vars[curr_literal->get_bool_index()];
                    curr_bool->inc_score();
                }
                for(var v : cls->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            m_total_clause_weight += m_unsat_clauses.size();
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
            LSTRACE(display_clause_weight(tout););
        }

        void smooth_clause_weight(){
            m_vars_visited.reset();
            for(clause_index i = 0; i < m_num_clauses; i++){
                nra_clause * curr_clause = m_nra_clauses[i];
                // smooth weight for sat clause with weight > 1
                if(!m_unsat_clauses.contains(i) && curr_clause->get_weight() > 1){
                    curr_clause->dec_weight();
                    m_total_clause_weight--;
                    // increase critical bool literal's score
                    if(curr_clause->get_sat_count() == 1){
                        SASSERT(curr_clause->get_critical_index() != null_var);
                        nra_literal const * curr_literal = m_nra_literals[curr_clause->get_critical_index()];
                        if(curr_literal->is_bool()){
                            nra_bool_var * curr_bool = m_bool_vars[curr_literal->get_bool_index()];
                            curr_bool->inc_score();
                        }
                    }
                }
                for(var v : curr_clause->m_vars) {
                    if (!m_vars_visited.contains(v)) {
                        m_vars_visited.insert(v);
                    }
                }
            }
            for (auto it = m_vars_visited.begin(); it != m_vars_visited.end(); it++){
                compute_boundary(*it);
            }
        }

        /**
         * Random Walk
         */
        void random_walk(){
            SASSERT(!m_unsat_clauses.empty());
            LSTRACE(tout << "start of random walk\n";);
            reset_arith_operation();
            m_bool_operation_index.reset();
            
            // intsert operations
            for(unsigned i = 0; i < 3 && m_bool_operation_index.size() + m_nra_operation_index.size() < 5; i++){
                // ^ random choose a clause
                clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                LSTRACE(tout << "consider clause "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                // LSTRACE(display_var_set(tout, curr_clause->m_arith_literals));
                // loop arith literals
                // ^ add arith literal operations in this clause
                for(literal_index l_idx: curr_clause->m_arith_literals){
                    nra_literal const * curr_literal = m_nra_literals[l_idx];
                    add_literal_arith_operation(curr_literal);   
                }
                // ^ add bool literal operations in this clause
                // loop bool literals
                for(literal_index l_idx: curr_clause->m_bool_literals){
                    nra_literal const * curr_literal = m_nra_literals[l_idx];
                    SASSERT(curr_literal->is_bool());
                    LSTRACE(tout << "consider literal "; m_solver.display(tout, curr_literal->m_literal); tout << std::endl;);
                    bool_var b = curr_literal->get_bool_index();
                    if(m_bool_is_chosen[b]){
                        continue;
                    }
                    m_bool_operation_index.push_back(b);
                    m_bool_is_chosen[b] = true;
                }
            }
            // end of insert operations, choose best operation (arith and bool)
            // restore chosen bool variables
            reset_chosen_bool();
            LSTRACE(tout << "[debug] nra size: " << m_nra_operation_index.size() << std::endl;
                display_arith_operations(tout);
            );
            LSCTRACE(m_nra_operation_index.empty() && m_bool_operation_index.empty(), tout << "stuck in random walk operation\n";);

            // make move
            if(m_bool_operation_index.size() + m_nra_operation_index.size() == 0){
                LSTRACE(tout << "empty operation, return\n";
                    show_ls_assignment(tout);
                );
                m_stuck++;
                m_stuck_ratio = 1.0 * m_stuck / m_step;
                no_operation_random_walk();
                return;
            }
            // arith move
            if(m_bool_operation_index.empty() || (m_bool_operation_index.size() > 0 && m_nra_operation_index.size() > 0 && !is_bool_search)){
                anum best_arith_value;
                literal_index best_literal_index;
                int best_arith_score = INT_MIN;
                var best_arith_index = select_best_from_arith_operations(best_arith_score, best_arith_value, best_literal_index);
                SASSERT(best_arith_index != null_var);
                LSTRACE(tout << "critical nra move in random walk\n";
                    tout << "best arith index: " << best_arith_index << std::endl;
                );
                critical_nra_move(best_arith_index, best_arith_value);
            }
            // bool move
            else {
                SASSERT(!m_bool_operation_index.empty());
                // loop bool operation
                int best_bool_score = INT_MIN;
                bool_var best_bool_index = select_best_from_bool_operations(best_bool_score);
                SASSERT(best_bool_index != null_var);
                LSTRACE(tout << "critical bool move in random walk\n";);
                critical_bool_move(best_bool_index);
            }
        }

        void no_operation_random_walk(){
            SASSERT(!m_unsat_clauses.empty());
            // ^ random select a clause
            clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
            nra_clause const * cls = m_nra_clauses[c_idx];
            SASSERT(cls->size() != 0);
            // ^ random select a literal
            literal_index l_idx = cls->m_literals[rand_int() % cls->size()];
            nra_literal const * lit = m_nra_literals[l_idx];
            // ^ bool critical move
            if(lit->is_bool()){
                critical_bool_move(lit->get_bool_index());
            }
            else {
                SASSERT(!lit->m_vars.empty());
                var_vector non_zero_coeff_vars;
                polynomial_ref lc(m_pm);
                polynomial_ref curr_p(m_pm);
                for(var v: lit->m_vars){
                    curr_p = get_atom_polys(lit->get_atom());
                    unsigned k = degree(curr_p, v);
                    lc = m_pm.coeff(curr_p, v, k);
                    if(m_am.eval_sign_at(lc, m_assignment) != 0){
                        non_zero_coeff_vars.push_back(v);
                    }
                }
                var picked_v = null_var;
                // random choose one var
                if(non_zero_coeff_vars.empty()){
                    picked_v = random_table(lit->m_vars);
                    SASSERT(picked_v != null_var);
                }
                else {
                    picked_v = non_zero_coeff_vars[rand_int() % non_zero_coeff_vars.size()];
                }
                // choose value for picked arith var
                anum w;
                nra_arith_var const * curr_arith = m_arith_vars[picked_v];
                scoped_anum old_value(m_am);
                m_am.set(old_value, m_assignment.value(picked_v));
                interval_set_ref old_value_interval(m_ism);
                // [old_value, old_value]
                old_value_interval = m_ism.mk_point_interval(old_value);
                if(m_var_value_fixed[picked_v]){
                    m_ism.peek_in_complement(old_value_interval, false, w, true);
                }
                else {
                    interval_set_ref curr_st(m_ism);
                    curr_st = m_ism.mk_union(old_value_interval, curr_arith->m_infeasible_st);
                    // happens for ==
                    // in this case, we ignore infeasible set, and choose a value except old value
                    if(m_ism.is_full(curr_st)){
                        m_var_value_fixed[picked_v] = true;
                        m_ism.peek_in_complement(old_value_interval, false, w, true);
                    }
                    // we sample values for the arith var, then check stuck situation
                    else {
                        anum_vector sample_values;
                        // m_ism.peek_in_complement(curr_st, false, w, true);
                        m_ism.peek_in_complement_heuristic(curr_st, sample_values);
                        bool still_stuck = true;
                        SASSERT(!sample_values.empty());
                        for(auto ele: sample_values){
                            m_assignment.set(picked_v, ele);
                            if(!is_literal_stuck(lit)){
                                m_am.set(w, ele);
                                // restore assignment
                                m_assignment.set(picked_v, old_value);
                                still_stuck = false;
                                break;
                            }
                            else {
                                // restore assignment
                                m_assignment.set(picked_v, old_value);
                            }
                        }
                        // still stuck, we random select one value
                        if(still_stuck){
                            LSTRACE(tout << "still stuck\n";);
                            // we use CAD
                            // if(!cad_move(lit, picked_v, w)){
                                LSTRACE(std::cout << "cad failed\n";);
                                LSTRACE(tout << "cad failed, we random choose a value\n";);
                                m_am.set(w, sample_values[rand_int() % sample_values.size()]);
                            // }
                            // else {
                                LSTRACE(std::cout << "cad succeed\n";);
                            // }
                        }
                    }
                }
                critical_nra_move(picked_v, w);
            }
        }

        void random_choose(var_vector const & vec, unsigned num, var_vector & res){
            res.reset();
            SASSERT(vec.size() > num && num > 0);
            for(unsigned i = 0; i < vec.size(); i++){
                if(i < num){
                    res.push_back(vec[i]);
                }
                else {
                    unsigned r = rand_int() % (i + 1);
                    if(r <= num - 1){
                        res[r] = vec[i];
                    }
                }
            }
        }

        void choose_sample(anum_vector const & vec, unsigned idx, anum & w){
            SASSERT(!vec.empty());
            SASSERT(i >= 0 && i < 2 * vec.size() + 1);
            // (-oo, vec[0])
            if(idx == 0){
                m_am.int_lt(vec[0], w);
                if(m_am.eq(vec[0], w)){
                    m_am.sub(w, m_one, w);
                }
            }
            // (vec.back, +Oo)
            else if(idx == 2 * vec.size()){
                m_am.int_gt(vec.back(), w);
                if(m_am.eq(vec.back(), w)){
                    m_am.add(w, m_one, w);
                }
            }
            else {
                if(idx % 2 == 1){
                    unsigned r_idx = idx / 2;
                    m_am.set(w, vec[r_idx]);
                }
                else {
                    unsigned l_idx = idx / 2 - 1, r_idx = idx / 2;
                    SASSERT(!m_am.eq(vec[l_idx], vec[r_idx]));
                    if(m_am.eq(vec[l_idx], vec[r_idx])){
                        UNREACHABLE();
                    }
                    m_am.select(vec[l_idx], vec[r_idx], w);
                }
            }
        }

        unsigned find_cell_index(anum_vector const & vec, anum const & w){
            if(vec.empty()){
                return 0;
            }
            // (-oo, vec[0])
            if(m_am.lt(w, vec[0])){
                return 0;
            }
            // (vec_back, +oo)
            if(m_am.gt(w, vec.back())){
                return 2 * vec.size();
            }
            // [vec_back, vec_back]
            if(m_am.eq(w, vec.back())){
                return 2 * vec.size() - 1;
            }
            for(unsigned i = 0; i < vec.size() - 1; i++){
                // [vec[i], vec[i]]
                if(m_am.eq(w, vec[i])){
                    return 2 * i + 1;
                }
                // (vec[i], vec[i+1])
                if(m_am.gt(w, vec[i]) && m_am.lt(w, vec[i + 1])){
                    return 2 * i + 2;
                }
            }
            UNREACHABLE();
        }

        void remove_duplicate(anum_vector & vec){
            unsigned j = 0;
            for(unsigned i = 0; i < vec.size(); i++){
                if(j == 0 || !m_am.eq(vec[i], vec[j - 1])){
                    m_am.set(vec[j], vec[i]);
                    j++;
                }
            }
            vec.shrink(j);
        }

        bool contains_value(anum_vector const & vec, anum const & w){
            for(auto ele: vec){
                if(m_am.eq(ele, w)){
                    return true;
                }
            }
            return false;
        }

        bool is_literal_stuck(nra_literal const * l){
            LSTRACE(tout << "enter literal stuck\n";);
            for(var v: l->m_vars){
                interval_set_ref curr_st(m_ism), union_st(m_ism);
                curr_st = m_evaluator.infeasible_intervals(l->get_atom(), l->sign(), nullptr, v);
                if(m_ism.is_full(curr_st)){
                    continue;
                }
                nra_arith_var const * curr_var = m_arith_vars[v];
                union_st = m_ism.mk_union(curr_st, curr_var->m_infeasible_st);
                if(m_ism.is_full(union_st)){
                    continue;
                }
                LSTRACE(tout << "exit literal stuck\n";);
                return false;
            }
            LSTRACE(tout << "exit literal stuck\n";);
            return true;
        }

        /**
         * Swap Operation
         */
        void add_swap_operation(){
            LSTRACE(tout << "start of add swap operation\n";);
            SASSERT(!m_sat_clause_with_false_literals.empty());
            if(m_sat_clause_with_false_literals.size() < 20){
                for(unsigned i = 0; i < m_sat_clause_with_false_literals.size(); i++){
                    nra_clause const * cls = m_nra_clauses[m_sat_clause_with_false_literals[i]];
                    for(literal_index l_idx: cls->m_arith_literals){
                        nra_literal const * lit = m_nra_literals[l_idx];
                        // only consider false literal
                        if(!lit->get_sat_status()){
                            add_literal_arith_operation(lit);   
                        }
                    }
                }
            }
            else {
                for(unsigned i = 0; m_nra_operation_index.size() < 20 && i < 50; i++){
                    clause_index c_idx = m_sat_clause_with_false_literals[rand_int() % m_sat_clause_with_false_literals.size()];
                    nra_clause const * cls = m_nra_clauses[c_idx];
                    for(literal_index l_idx: cls->m_arith_literals){
                        nra_literal const * lit = m_nra_literals[l_idx];
                        if(!lit->get_sat_status()){
                            add_literal_arith_operation(lit);
                        }
                    }
                }
            }
            LSTRACE(tout << "end of add swap operation\n";);
        }


        // TRACE
        // std::ostream & check_solution_sat(std::ostream & out){
        //     show_ls_assignment(out);
        //     for(literal_index i = 0; i < m_nra_literals.size(); i++){
        //         m_solver.display(out, m_nra_literals[i]->m_literal); out << std::endl;
        //         nra_literal const * l = m_nra_literals[i];
        //         if(l->is_bool()){
        //             out << "bool value: " << (m_bool_vars[l->get_bool_index()]->get_value() ? "true" : "false") << std::endl;
        //         }
        //         else {
        //             ineq_atom const * aa = l->get_atom();
        //             SASSERT(aa->size() > 0);
        //             scoped_anum curr(m_am);
        //             m_am.set(curr, 1);
        //             for(unsigned i = 0; i < aa->size(); i++){
        //                 poly * p = aa->p(i);
        //                 scoped_anum p_value(m_am);
        //                 m_pm.eval(p, m_assignment, p_value);
        //                 m_am.mul(curr, p_value, curr);
        //             }
        //             out << "value: "; m_am.display(out, curr); out << std::endl;
        //         }
        //     }
        //     return out;
        // }

        void propagate_sub_values(){
            for(auto ele: m_sub_value){
                var v = ele.m_var;
                poly const * p = ele.p, * q = ele.q;
                // v = q / p
                scoped_anum p_val(m_am), q_val(m_am), val(m_am);
                m_pm.eval(p, m_assignment, p_val);
                m_pm.eval(q, m_assignment, q_val);
                m_am.div(q_val, p_val, val);
                m_assignment.set(v, val);
            }
        }

        int get_total_weight() {
            int result = 0;
            for (int i = 0; i < m_unsat_clauses.size(); i++) {
                clause_index curr_index = m_unsat_clauses[i];
                nra_clause const * curr_clause = m_nra_clauses[curr_index];
                result += curr_clause->get_weight();
            }
            return result;
        }

        void slack_equation(clause_index c_idx, var picked_var, anum const & value) {
            if(!m_slacked_clauses.contains(c_idx)) {
                m_slacked_clauses.insert(c_idx);
            }
            // TODO: slack var's assignment or equalities
        }

        /**
         * Local Search
         */
        lbool local_search(){
            SPLIT_LINE(tout);
            // std::cout << "begin" << std::endl;
            LSTRACE(tout << "local search begin\n";
                std::cout << "local search begin\n";
            );
            SPLIT_LINE(tout);
            no_improve_cnt = 0;
            m_start_time = std::chrono::steady_clock::now();
            m_step = 0;
            // analyze_problem();
            // ICP returns false
            if(!init_solution(true)){
                LSTRACE(std::cout << "ICP returns false\n";);
                LSTRACE(tout << "ICP returns false\n";);
                return l_false;
            }
            m_outer_step = 1;
            for(m_step = 1; m_step < max_step; m_step++){
                // if (m_step % 100 == 0) {
                //     std::cout << "step: " << m_step << " #unsat clauses: " << m_unsat_clauses.size() << std::endl;
                // }
                m_stuck_ratio = 1.0 * m_stuck / m_step;
                LSTRACE(tout << "step: " << m_step << std::endl;
                    tout << "no improve cnt: " << no_improve_cnt << std::endl;
                );
                is_random_walk = (rand_int() % 100 < 30);
                // if (is_random_walk) {
                //     if (no_improve_cnt_mode > 500) {
                //         is_random_walk = false;  // change to greedy mode
                //         no_improve_cnt_mode = 0;
                //     } 
                // } else {
                //     if (no_improve_cnt_mode > 1000) {
                //         is_random_walk = true;   // change to random walk mode
                //         no_improve_cnt_mode = 0;
                //     }
                // }
                // Succeed
                if(m_unsat_clauses.empty()){
                    SPLIT_LINE(std::cout);
                    LSTRACE(
                        std::cout << "local search succeed\n";
                        tout << "local search succeed\n";
                    );
                    SPLIT_LINE(std::cout);
                    
                    collect_bool_values();
                    check_solution_sat();
                    propagate_sub_values();
                    return l_true;
                }
                // Fail
                if(TimeElapsed() > m_cutoff && m_step % 100 == 0){
                    SPLIT_LINE(std::cout);
                    LSTRACE(std::cout << "local search failed\n";);
                    SPLIT_LINE(std::cout);
                    return l_undef;
                }
                // Main
                LSTRACE(tout << "enter main procedure\n";);
                bool time_up_bool = no_improve_cnt_bool * m_num_unsat_literals > 5 * m_num_bool_unsat_literals;
                bool time_up_nra = no_improve_cnt_nra * m_num_unsat_literals > 20 * (m_num_unsat_literals - m_num_bool_unsat_literals);
                // Choose Mode
                if(m_num_bool_unsat_literals == 0 || (is_bool_search && time_up_bool && m_num_bool_unsat_literals < m_num_unsat_literals)){
                    enter_nra_mode();
                }
                else if(m_num_unsat_literals == m_num_bool_unsat_literals || (!is_bool_search && time_up_nra && m_num_bool_unsat_literals > 0)){
                    enter_bool_mode();
                }
                // Search

                // pick bool variable
                bool_var picked_b;
                var picked_v;
                scoped_anum next_value(m_am);
                int best_score;
                bool pick_eq;
                clause_index eq_idx;
                int mode = pick_critical_move(picked_b, picked_v, next_value, best_score, pick_eq, eq_idx);

                int before_weight = get_total_weight();
                if (mode == 0) {  // bool operation
                    critical_bool_move(picked_b);
                    if(update_bool_info()){
                        no_improve_cnt_bool = 0;
                    }
                    else {
                        no_improve_cnt_bool++;
                    }
                    SASSERT(before_weight - get_total_weight() == best_score);
                } else if (mode == 1) {  // arith operation
                    if(use_equation_slack && pick_eq && !is_simpler(next_value, m_min)) { // can only happen for greedy cases
                        slack_equation(eq_idx, picked_v, next_value);
                    }
                    critical_nra_move(picked_v, next_value);
                    // update arith improvement
                    if(update_nra_info()){
                        no_improve_cnt_nra = 0;
                    }
                    else {
                        no_improve_cnt_nra++;
                    }
                    SASSERT(before_weight - get_total_weight() == best_score);
                } else {
                    // No operation
                }

                // update improvement
                if(update_solution_info()){
                    no_improve_cnt = 0;
                    no_improve_cnt_mode = 0;
                }
                else {
                    no_improve_cnt++;
                    no_improve_cnt_mode++;
                }

                // Restart
                if(no_improve_cnt > m_restart_count){
                    LSTRACE(tout << "no improve count: " << no_improve_cnt << std::endl;
                        tout << "restart\n";
                        SPLIT_LINE(std::cout);
                        SPLIT_LINE(tout);
                        std::cout << "no improve, restart\n";
                        SPLIT_LINE(std::cout);
                        SPLIT_LINE(tout);
                    );
                    init_solution(false);
                    no_improve_cnt = 0;
                    m_restart_count *= 2;
                    use_infeasible_st = !use_infeasible_st;
                }
            }
            SPLIT_LINE(std::cout);
            LSTRACE(std::cout << "local search failed\n";);
            SPLIT_LINE(std::cout);
            return l_undef;
        }

        void check_solution_sat() const {
            for(unsigned i = 0; i < m_nra_clauses.size(); i++){
                if(!is_clause_sat(m_nra_clauses[i])){
                    UNREACHABLE();
                }
            }
        }

        bool is_clause_sat(nra_clause const * cls) const {
            for(literal_index l_idx: cls->m_literals){
                nra_literal const * l = m_nra_literals[l_idx];
                if(is_literal_sat(l)){
                    return true;
                }
            }
            return false;
        }

        bool is_literal_sat(nra_literal const * l) const {
            if(l->is_bool()){
                nra_bool_var const * b = m_bool_vars[l->get_bool_index()];
                return l->sign() != b->get_value();
            }
            else {
                return m_evaluator.eval((atom * ) l->get_atom(), l->sign());
            }
        }

        /**
         * Display
         */
        std::ostream & display_const_anum(std::ostream & out) const {
            out << "show constant anum\n";
            m_am.display(out << "m_zero: ", m_zero) << std::endl;
            m_am.display(out << "m_one: ", m_one) << std::endl;
            m_am.display(out << "m_min: ", m_min) << std::endl;
            return out;
        }

        std::ostream & show_ls_assignment(std::ostream & out) const {
            for(bool_var b = 0; b < m_bool_vars.size(); b++){
                nra_bool_var const * b_var = m_bool_vars[b];
                out << "b" << b << ": " << (b_var->get_value() ? "true" : "false") << std::endl;
            }
            m_assignment.display(out);
            return out;
        }

        std::ostream & display_var_vector(std::ostream & out, var_vector const & vec) const {
            for(var v = 0; v < vec.size(); v++){
                out << v << " -> " << vec[v] << std::endl;
            }
            return out;
        }

        std::ostream & display_var_set(std::ostream & out, var_vector const & vec) const {
            for(var v: vec){
                out << v << " ";
            }
            return out;
        }

        std::ostream & display_var_table(std::ostream & out, var_table const & vec) const {
            for(var v: vec){
                out << v << " ";
            }
            return out;
        }

        std::ostream & display_literal_set(std::ostream & out, var_vector const & vec) const {
            for(literal_index v: vec){
                literal l = m_nra_literals[v]->m_literal;
                m_solver.display(out, l);
                out << " ";
            }
            return out;
        }

        std::ostream & display_clause_set(std::ostream & out, var_vector const & vec) const {
            for(clause_index v: vec){
                clause const & cls = *m_clauses[v];
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_bool(std::ostream & out, bool b) const {
            out << (b ? "true" : "false");
            return out;
        }

        std::ostream & display_arith_operations(std::ostream & out) const {
            out << "show arith operations\n";
            SASSERT(m_nra_operation_index.size() == m_nra_operation_value.size());
            if(m_nra_operation_index.empty()){
                out << "operation is empty\n";
                show_ls_assignment(out);
            }
            for(unsigned i = 0; i < m_nra_operation_index.size(); i++){
                out << "var: " << m_nra_operation_index[i] << "  ";
                out << "value: "; m_am.display(out, m_nra_operation_value[i]);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_arith_intervals(std::ostream & out) const {
            for(var v = 0; v < m_arith_vars.size(); v++){
                nra_arith_var const * curr = m_arith_vars[v];
                out << v << ": " << "feasible: ";
                m_ism.display(out, curr->m_feasible_st);
                out << "  " << "infeasible: ";
                m_ism.display(out, curr->m_infeasible_st);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_clause_info(std::ostream & out, nra_clause const * c) const {
            out << "show clause info:\n";
            out << "clause: "; m_solver.display(out, *c->get_clause()); out << std::endl;
            out << "sat count: " << c->get_sat_count() << std::endl;
            out << "sat status: " << (c->get_sat_status() ? "true" : "false") << std::endl;
            return out;
        }

        std::ostream & display_vars(std::ostream & out) const {
            out << "display arith vars\n";
            for(var v = 0; v < m_num_vars; v++){
                out << v << "  ";
                m_solver.display_var(out, v);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_clauses(std::ostream & out) const {
            out << "display clauses\n";
            for(clause_index c = 0; c < m_clauses.size(); c++){
                const clause & cls = *(m_clauses[c]);
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_unit_clauses(std::ostream & out) const {
            out << "display unit clauses\n";
            for(clause_index cls_idx: m_unit_clauses){
                const clause & cls = *(m_clauses[cls_idx]);
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_unsat_clauses(std::ostream & out) const {
            out << "display unsat clauses\n";
            if(m_unsat_clauses.empty()){
                out << "no unsat clauses\n";
            }
            for(clause_index cls_idx: m_unsat_clauses){
                const clause & cls = *(m_clauses[cls_idx]);
                m_solver.display(out, cls);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_literal_vector(std::ostream & out, var_vector const & vec) const {
            out << "show literal index vector\n";
            for(unsigned i = 0; i < vec.size(); i++){
                out << i << " ";
                m_solver.display(out, m_nra_literals[vec[i]]->m_literal);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_bool_vector(std::ostream & out, bool_vector const & vec) const {
            out << "show bool vector\n";
            for(unsigned i = 0; i < vec.size(); i++){
                out << i << " ";
                out << (vec[i] ? "true" : "false");
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_anum_vector(std::ostream & out, anum_vector const & vec) const {
            out << "show anum vector\n";
            for(unsigned i = 0; i < vec.size(); i++){
                out << "[" << i << "] ";
                m_am.display(out, vec[i]);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_clause_weight(std::ostream & out) const {
            out << "display clause weights\n";
            for(clause_index i = 0; i < m_nra_clauses.size(); i++){
                const clause & cls = *(m_nra_clauses[i]->get_clause());
                m_solver.display(out, cls);
                out << std::endl;
                out << "weight: " << m_nra_clauses[i]->get_weight() << std::endl;
            }
            return out;
        }

        // std::ostream & display_anum_value_vector(std::ostream & out, anum_value_vector const & vec) const {
        //     for(unsigned i = 0; i < vec.size(); i++){
        //         m_am.display(out, vec[i].w); out << " ";
        //     }
        //     out << std::endl;
        //     return out;
        // }

        std::ostream & display_poly_vector(std::ostream & out, polynomial_ref_vector const & vec) const {
            for(unsigned i = 0; i < vec.size(); i++){
                polynomial_ref ele(m_pm);
                ele = vec.get(i);
                m_pm.display(out, ele);
                out << std::endl;
            }
            return out;
        }
    };

    ls_helper::ls_helper(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, svector<lbool> & bvalues, clause_vector & cls, atom_vector const & ats, unsigned_vector const & eq_cls, bool_var_vector const & pure_bool_vars, 
                         bool_var_vector const & pure_bool_convert, 
                        unsigned seed, unsigned & step, unsigned & stuck, double & ratio, substitute_value_vector const & vec
                         ){
        m_imp = alloc(imp, s, am, pm, cache, ism, ev, ass, bvalues, cls, ats, eq_cls, pure_bool_vars, pure_bool_convert, seed, step, stuck, ratio, vec);
    }

    ls_helper::~ls_helper(){
        dealloc(m_imp);
    }

    void ls_helper::set_var_num(unsigned x){
        m_imp->set_var_num(x);
    }

    lbool ls_helper::local_search(){
        return m_imp->local_search();
    }
};