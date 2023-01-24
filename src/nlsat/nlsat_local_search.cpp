#include "nlsat/nlsat_local_search.h"
#include "util/heap.h"

/**
 * 22/10/10: substitution
*            meti-tarski: a1 x+b1 y = 0, a2 x^2 + b2 y^2 = d
 * 
*/

namespace nlsat {
    struct clause_var_number_lt {
        const nra_clause_vector & vec;
        clause_var_number_lt(const nra_clause_vector & v): vec(v) {}

        bool operator()(clause_index x, clause_index y) const {
            return vec[x]->get_left_vars() < vec[y]->get_left_vars();
        }
    };

    struct ls_helper::imp {
        // Basic
        solver & m_solver;
        evaluator & m_evaluator;
        anum_manager & m_am;
        pmanager & m_pm;
        polynomial::cache &     m_cache;
        interval_set_manager & m_ism;

        // Assignment
        assignment & m_assignment;
        bool_vector m_bool_result;

        typedef ptr_vector<interval_set> interval_set_vector;
        // interval_set_vector m_var_init_st;
        bool_vector m_var_value_fixed;

        /**
         * Const Anum
         * Zero: 0
         * One: 1
         * Delta: 1/max
         * Max: INT_MAX
         */
        anum m_zero, m_one, m_two, m_min, m_max;

        /**
         * Arith Var
         */
        nra_arith_var_vector m_arith_vars;
        var_table m_vars_visited;
        var_table m_literal_added;
        // used for calculating bound assignment
        // var_vector m_irra_vars;
        // anum_vector m_var_values;
        
        /**
         * Bool Var
         */
        nra_bool_var_vector m_bool_vars;
        var_vector m_bool_convert;
        bool_var m_max_bool_var;

        /**
         * Literal
         */
        nra_literal_vector m_nra_literals;
        var m_num_bool_literals;
        var m_num_arith_literals;
        
        literal_vector m_literal_visited;
        // used for set literal anum
        var_vector m_literal_index_visited;
        // store before sat information
        bool_vector m_literal_before_sat;

        /**
         * Count duplicated literals in various clauses
         */
        unsigned m_num_unsat_literals;
        unsigned m_num_bool_unsat_literals;

        /**
         * Clause
         */
        const clause_vector & m_clauses;
        nra_clause_vector m_nra_clauses;
        // used to get var's interval set (ignore in main search)
        // only contain just one arith variable
        var_table m_unit_var_clauses;
        // only contain one literal
        var_table m_unit_clauses;
        // unsat clauses (index)
        var_vector m_unsat_clauses;
        // unsat clauses with pure bool var (index)
        var_table m_unsat_clauses_bool;
        // sat clause with false literals (index)
        var_vector m_sat_clause_with_false_literals;
        unsigned m_total_clause_weight;

        /**
         * Atoms
         */
        const atom_vector & m_atoms;
        // dead bool vars
        const bool_vector & m_dead;

        /**
         * Information
         */
        var m_num_vars;
        var m_num_bool_vars;
        var m_num_literals;
        var m_num_clauses;

        /**
         * Random
         */
        unsigned m_rand_seed;

        /**
         * Solution
         */
        // unsigned m_best_found_cost;
        unsigned m_best_found_restart;
        unsigned no_improve_cnt_bool;
        unsigned no_improve_cnt_nra;
        unsigned no_improve_cnt;
        unsigned m_best_found_cost_bool;
        unsigned m_best_found_cost_nra;

        /**
         * Control
         */
        var & m_step;
        var m_outer_step;
        unsigned m_num_arith_opt, m_num_bool_opt;
        const unsigned max_step = UINT_MAX;
        int m_cc_mode;
        std::chrono::steady_clock::time_point m_start_time;
        int m_time_label;
        double m_best_cost_time;
        double m_cutoff;
        bool use_swap;
        bool is_bool_search;
        const unsigned smooth_probability = 3;

        /**
         * Operation
         */
        unsigned & m_pair_cm;
        bool_vector m_bool_is_chosen;
        bool_var_vector m_bool_operation_index;
        
        anum_table m_nra_operation_table_level1;
        var_vector m_nra_operation_index_level1;
        anum_vector m_nra_operation_value_level1;
        var_vector m_nra_operation_literal_index_level1;

        anum_table m_nra_operation_table_level2;
        var_vector m_nra_operation_index_level2;
        anum_vector m_nra_operation_value_level2;
        var_vector m_nra_operation_literal_index_level2;

        unsigned & m_stuck;
        double & m_stuck_ratio;
        unsigned & m_cad_move;
        unsigned & m_cad_succeed;
        unsigned & m_poly_bound;
        const bool use_factor = true;
        polynomial_ref_vector temp_factors;

        const substitute_value_vector & m_sub_value;
        

        imp(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, clause_vector const & cls, atom_vector const & ats, bool_vector const & dead, unsigned seed,
                         unsigned & step, unsigned & stuck, double & ratio, unsigned & cad_move, unsigned & cad_succeed, unsigned & poly_bound,
                         unsigned & pair_cm, substitute_value_vector const & vec)
        : m_am(am), m_pm(pm), m_ism(ism), m_evaluator(ev), m_assignment(ass), m_clauses(cls), 
        m_atoms(ats), m_rand_seed(seed), m_solver(s), m_cc_mode(-1), m_cutoff(1200), is_bool_search(false),
        m_time_label(1), m_nra_operation_table_level1(m_am, m_nra_operation_index_level1, m_nra_operation_value_level1),
        m_step(step), m_stuck(stuck), m_stuck_ratio(ratio), m_cache(cache), m_cad_move(cad_move), m_cad_succeed(cad_succeed),
        temp_factors(m_pm), m_poly_bound(poly_bound), m_pair_cm(pair_cm), m_dead(dead), m_sub_value(vec), 
        m_nra_operation_table_level2(m_am, m_nra_operation_index_level2, m_nra_operation_value_level2)
        {
            set_const_anum();
            clear_statistics();
        }


        ~imp(){
            clear();
        }

        void clear_statistics(){
            m_stuck = 0;
            m_stuck_ratio = 0;
            m_cad_move = 0;
            m_cad_succeed = 0;
            m_poly_bound = 0;
        }

        void clear(){
            LSTRACE(std::cout << "local search imp deleted\n";);
        }

        /**
         * Initialize
         */
        void set_var_num(unsigned x){
            LSTRACE(tout << "set arith variable number: " << x << std::endl;
                std::cout << "start of set arith variable number\n";
            );
            m_num_vars = x;
            LSTRACE(display_vars(tout); display_clauses(tout););
            init_bool_vars();
            init_bool_convert();
            init_arith_vars();
            init_clauses();
            // if(x <= 5){
            //     m_pair_cm = 0;
            //     // m_pair_cm = 1;
            // } else {
            //     m_pair_cm = 0;
            // }
            m_pair_cm = 0;
            LSCTRACE(m_pair_cm == 1, 
                tout << "--------------------------enable pair literal move--------------------------\n";
                std::cout << "--------------------------enable pair literal move--------------------------\n";
            );
            LSCTRACE(m_pair_cm == 0, 
                tout << "--------------------------disable pair literal move--------------------------\n";
                std::cout << "--------------------------disable pair literal move--------------------------\n";
            );
            LSTRACE(tout << "end of set arith variable numbers" << std::endl;
                std::cout << "end of set arith variable number\n";
            );
        }

        void init_bool_vars(){
            m_bool_vars.reset();
            m_max_bool_var = 0;
            m_num_bool_vars = 0;
            bool_var curr_index = 0;
            for(bool_var b = 0; b < m_atoms.size(); b++){
                if(m_atoms[b] == nullptr && !m_dead[b]){
                    m_num_bool_vars++;
                    nra_bool_var * temp_bvar = new nra_bool_var(curr_index, b);
                    m_bool_vars.push_back(temp_bvar);
                    curr_index++;
                    SASSERT(b >= m_max_bool_var);
                    m_max_bool_var = b;
                }
            }
            m_bool_is_chosen.resize(m_num_bool_vars, false);
            LSTRACE(tout << "number of pure bool variables: " << m_num_bool_vars << std::endl;);
        }

        void init_bool_convert(){
            m_bool_convert.resize(m_max_bool_var + 1, UINT_MAX);
            for(bool_var b = 0; b < m_bool_vars.size(); b++){
                m_bool_convert[m_bool_vars[b]->get_origin_index()] = m_bool_vars[b]->get_index();
            }
            LSTRACE(tout << "show bool convert\n";
                display_var_vector(tout, m_bool_convert);
            );
        }

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

        void init_arith_infeasible_set(){
            // m_var_init_st.reset();
            m_var_value_fixed.resize(m_arith_vars.size(), false);
            for(var v = 0; v < m_arith_vars.size(); v++){
                nra_arith_var * curr = m_arith_vars[v];
                curr->m_infeasible_st = m_ism.mk_complement(curr->m_feasible_st);
            }
        }

        void init_literal(literal l){
            LSTRACE(tout << "init literal "; m_solver.display(tout, l); tout << std::endl;);
            bool is_bool = is_bool_literal(l);
            // bool literal: pure bool index
            // arith literal: null_var
            bool_var b_idx = is_bool ? m_bool_convert[l.var()] : null_var;
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

        /**
         * Init Solution
         */
        // false means ICP returns unsat
        // only ICP for the first initialize
        bool init_solution(bool first_init){
            LSTRACE(tout << "start of init solution\n";);
            if(!init_assignment(first_init)){
                return false;
            }
            init_literals_delta();
            init_clauses_delta();
            m_best_found_restart = m_num_clauses;
            update_solution_info();
            m_best_found_cost_bool = UINT_MAX;
            m_best_found_cost_nra = UINT_MAX;
            LSTRACE(tout << "end of init solution\n";
                display_unsat_clauses(tout);
            );
            return true;
        }

        // TODO: var value propagation CNC
        bool init_assignment(bool first_init){
            LSTRACE(tout << "start of init assignment\n";);
            if(first_init){
                m_assignment.reset();
                for(bool_var b = 0; b < m_num_bool_vars; b++){
                    m_bool_vars[b]->set_value(true);
                }
                for(var v = 0; v < m_num_vars; v++){
                    nra_arith_var const * curr_arith = m_arith_vars[v];
                    // infeasible set full
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
                
                // init use swap
                use_swap = false;
                LSTRACE(tout << "end of init assignment\n";
                    show_ls_assignment(tout);
                );
                return true;
            }
            // consider old value
            else {
                use_swap = false;
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
                    if(curr_arith->m_infeasible_st != nullptr){
                        m_ism.inc_ref(curr_arith->m_infeasible_st);
                    }
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
            m_am.set(m_max, INT_MAX);
            m_am.div(m_one, m_max, m_min);
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
                // std::cout << "elapsed: " << res << " s" << std::endl;
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

        void insert_in_complement_level1(var v, interval_set const * s, literal_index l_idx){
            SASSERT(!m_ism.is_full(s));
            LSTRACE(
                tout << "insertion var " << v << std::endl;
                tout << "show set of insert: "; m_ism.display(tout, s); tout << std::endl;
            );
            anum_vector w_vec;
            m_ism.peek_in_complement_heuristic_level1(s, w_vec);
            for(auto ele: w_vec){
                if(m_assignment.is_assigned(v) && m_am.eq(ele, m_assignment.value(v))){
                    continue;
                }
                if(m_nra_operation_table_level1.contains(v, ele)){
                    continue;
                }
                m_nra_operation_index_level1.push_back(v);
                m_nra_operation_value_level1.push_back(ele);
                m_nra_operation_literal_index_level1.push_back(l_idx);
            }
        }

        void insert_in_complement_level2(var v, interval_set const * s, literal_index l_idx) {
            SASSERT(!m_ism.is_full(s));
            LSTRACE(
                tout << "insertion var " << v << std::endl;
                tout << "show set of insert: "; m_ism.display(tout, s); tout << std::endl;
            );
            anum_vector w_vec;
            m_ism.peek_in_complement_heuristic_level2(s, w_vec);
            for(auto ele: w_vec){
                if(m_assignment.is_assigned(v) && m_am.eq(ele, m_assignment.value(v))){
                    continue;
                }
                if(m_nra_operation_table_level2.contains(v, ele)){
                    continue;
                }
                m_nra_operation_index_level2.push_back(v);
                m_nra_operation_value_level2.push_back(ele);
                m_nra_operation_literal_index_level2.push_back(l_idx);
            }
        }

        unsigned rand_int(){
            random_gen r(m_rand_seed++);
            return r();
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
            m_bool_result.reset();
            for(bool_var b = 0; b < m_bool_vars.size(); b++){
                m_bool_result.push_back(m_bool_vars[b]->get_value());
            }
        }

        bool_var select_best_from_bool_operations(int & best_score){
            // set BMS and cnt
            unsigned cnt;
            bool BMS;
            if(m_bool_operation_index.size() > 45){
                BMS = true;
                cnt = 45;
            }
            else {
                BMS = false;
                cnt = m_bool_operation_index.size();
            }
            unsigned best_last_move = UINT_MAX;
            bool_var m_curr_operation, best_bool_var_index = null_var;
            // loop bool operations
            for(unsigned i = 0; i < cnt; i++){
                if(BMS){
                    // swap
                    unsigned rand_index = rand_int() % (m_bool_operation_index.size() - i);
                    unsigned temp = m_bool_operation_index[m_bool_operation_index.size() - i - 1];
                    m_curr_operation = m_bool_operation_index[rand_index];
                    m_bool_operation_index[rand_index] = temp;
                } 
                else {
                    m_curr_operation = m_bool_operation_index[i];
                }
                // Score for pure bool variables are calculated before
                nra_bool_var const * curr_bool = m_bool_vars[m_curr_operation];
                if(curr_bool->get_score() > best_score || (curr_bool->get_score() == best_score && curr_bool->get_last_move() < best_last_move)){
                    best_score = curr_bool->get_score();
                    best_last_move = curr_bool->get_last_move();
                    best_bool_var_index = m_curr_operation;
                }
            }
            return best_bool_var_index;
        }

        /**
         * Critical Move
         */
        bool_var pick_critical_bool_move(){
            LSTRACE(tout << "show time of start picking bool move\n";
                TimeElapsed();
            );
            LSTRACE(tout << "start of pick bool move\n";
                show_ls_assignment(tout);
            );
            m_bool_operation_index.reset();
            for(clause_index cls_idx: m_unsat_clauses_bool){
                nra_clause const * curr_clause = m_nra_clauses[cls_idx];
                for(literal_index lit_index: curr_clause->m_bool_literals){
                    nra_literal const * curr_literal = m_nra_literals[lit_index];
                    bool_var idx = curr_literal->get_bool_index();
                    // ignore chosen bool var
                    if(m_bool_is_chosen[idx]){
                        continue;
                    }
                    nra_bool_var const * curr_bool = m_bool_vars[idx];
                    // not in tabulist, choose the bool var
                    if(m_step > curr_bool->get_tabu()){
                        m_bool_is_chosen[idx] = true;
                        m_bool_operation_index.push_back(idx);
                    }
                }
            }
            // reset is chosen to false
            reset_chosen_bool();
            int best_bool_score = 1;
            bool_var best_bool_var_index = select_best_from_bool_operations(best_bool_score);
            // untabu decreasing bool variable exists
            if(best_bool_var_index != null_var){
                LSTRACE(tout << "end of pick bool move\n";);
                LSTRACE(tout << "show time of end picking bool move\n";
                    TimeElapsed();
                );
                return best_bool_var_index;
            }
            // update clause weight
            if(rand_int() % 10000 > smooth_probability){
                update_clause_weight();
            }
            else {
                smooth_clause_weight();
            }

            if (m_bool_operation_index.size() > 0) {
                unsigned rand_index = rand_int() % (m_bool_operation_index.size());
                return m_bool_operation_index[rand_index];
            }
            // random_walk();
            LSTRACE(tout << "end of pick bool move\n";);
            LSTRACE(tout << "show time of end picking bool move\n";
                TimeElapsed();
            );
            return null_var;
        }

        void reset_chosen_bool(){
            for(bool_var idx: m_bool_operation_index){
                m_bool_is_chosen[idx] = false;
            }
        }

        var select_best_from_arith_operations_level1(int & best_score, anum & best_value, literal_index & best_literal_index){
            bool BMS;
            unsigned cnt;
            var m_arith_index;
            scoped_anum m_arith_value(m_am);
            literal_index m_literal_index;
            if(m_nra_operation_index_level1.size() > 45){
                cnt = 45;
                BMS = true;
            }
            else {
                BMS = false;
                cnt = m_nra_operation_index_level1.size();
            }
            LSTRACE(
                if(BMS){
                    tout << "BMS enabled\n";
                } else {
                    tout << "BMS disabled\n";
                }
            );
            unsigned best_last_move = UINT_MAX, best_arith_index = null_var;
            best_literal_index = null_var;
            for(unsigned i = 0; i < cnt; i++){
                if(BMS){
                    // swap
                    unsigned rand_index = rand_int() % (m_nra_operation_index_level1.size() - i);
                    m_arith_index = m_nra_operation_index_level1[rand_index];
                    m_literal_index = m_nra_operation_literal_index_level1[rand_index];
                    m_am.set(m_arith_value, m_nra_operation_value_level1[rand_index]);
                    m_nra_operation_index_level1[rand_index] = m_nra_operation_index_level1[m_nra_operation_index_level1.size() - i - 1];
                    m_am.set(m_nra_operation_value_level1[rand_index], m_nra_operation_value_level1[m_nra_operation_index_level1.size() - i - 1]);;
                    m_nra_operation_literal_index_level1[rand_index] = m_nra_operation_literal_index_level1[m_nra_operation_index_level1.size() - i - 1];
                }
                else {
                    m_arith_index = m_nra_operation_index_level1[i];
                    m_literal_index = m_nra_operation_literal_index_level1[i];
                    m_am.set(m_arith_value, m_nra_operation_value_level1[i]);
                }
                int curr_score = get_arith_critical_score(m_arith_index, m_arith_value);
                LSTRACE(tout << "show score in pick nra move: " << curr_score << std::endl;);
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

        var select_best_from_arith_operations(int & best_score, anum & best_value, literal_index & best_literal_index){
            int origin_best_score = best_score;

            scoped_anum best_value_level1(m_am), best_value_level2(m_am);
            literal_index best_literal_index_level1, best_literal_index_level2;
            var v1 = select_best_from_arith_operations_level1(best_score, best_value, best_literal_index);
            m_am.set(best_value_level1, best_value);
            best_literal_index_level1 = best_literal_index;
            int best_score_level1 = best_score;
            
            best_score = origin_best_score;
            var v2 = select_best_from_arith_operations_level2(best_score, best_value, best_literal_index);
            m_am.set(best_value_level2, best_value);
            best_literal_index_level2 = best_literal_index;
            int best_score_level2 = best_score;

            if(v1 == null_var) {
                best_score = best_score_level2;
                m_am.set(best_value, best_value_level2);
                best_literal_index = best_literal_index_level2;
                return v2;
            }
            else if(v2 == null_var) {
                best_score = best_score_level1;
                m_am.set(best_value, best_value_level1);
                best_literal_index = best_literal_index_level1;
                return v1;
            }
            else {
                if(best_score_level1 > best_score_level2) {
                    best_score = best_score_level1;
                    m_am.set(best_value, best_value_level1);
                    best_literal_index = best_literal_index_level1;
                    return v1;
                }
                else {
                    best_score = best_score_level2;
                    m_am.set(best_value, best_value_level2);
                    best_literal_index = best_literal_index_level2;
                    return v2;
                }
            }
        }

        var select_best_from_arith_operations_level2(int & best_score, anum & best_value, literal_index & best_literal_index){
            bool BMS;
            unsigned cnt;
            var m_arith_index;
            scoped_anum m_arith_value(m_am);
            literal_index m_literal_index;
            if(m_nra_operation_index_level2.size() > 45){
                cnt = 45;
                BMS = true;
            }
            else {
                BMS = false;
                cnt = m_nra_operation_index_level2.size();
            }
            LSTRACE(
                if(BMS){
                    tout << "BMS enabled\n";
                } else {
                    tout << "BMS disabled\n";
                }
            );
            unsigned best_last_move = UINT_MAX, best_arith_index = null_var;
            best_literal_index = null_var;
            for(unsigned i = 0; i < cnt; i++){
                if(BMS){
                    // swap
                    unsigned rand_index = rand_int() % (m_nra_operation_index_level2.size() - i);
                    m_arith_index = m_nra_operation_index_level2[rand_index];
                    m_literal_index = m_nra_operation_literal_index_level2[rand_index];
                    m_am.set(m_arith_value, m_nra_operation_value_level2[rand_index]);
                    m_nra_operation_index_level2[rand_index] = m_nra_operation_index_level2[m_nra_operation_index_level2.size() - i - 1];
                    m_am.set(m_nra_operation_value_level2[rand_index], m_nra_operation_value_level2[m_nra_operation_index_level2.size() - i - 1]);;
                    m_nra_operation_literal_index_level2[rand_index] = m_nra_operation_literal_index_level2[m_nra_operation_index_level2.size() - i - 1];
                }
                else {
                    m_arith_index = m_nra_operation_index_level2[i];
                    m_literal_index = m_nra_operation_literal_index_level2[i];
                    m_am.set(m_arith_value, m_nra_operation_value_level2[i]);
                }
                int curr_score = get_arith_critical_score(m_arith_index, m_arith_value);
                LSTRACE(tout << "show score in pick nra move: " << curr_score << std::endl;);
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

        unsigned pair_code(nra_literal const * l1, nra_literal const * l2) const {
            unsigned id1 = l1->get_index(), id2 = l2->get_index();
            SASSERT(id1 != id2);
            if(id1 > id2){
                unsigned copy = id1;
                id1 = id2;
                id2 = copy;
            }
            return id1 * m_nra_literals.size() + id2;
        }

        void add_pair_literal_arith_operation(nra_literal const * l1, nra_literal const * l2){
            if(l1->get_index() == l2->get_index()){
                return;
            }
            LSTRACE(tout << "add pair operation for literal\n";
                m_solver.display(tout, l1->m_literal); tout << std::endl;
                m_solver.display(tout, l2->m_literal); tout << std::endl;
            );
            unsigned index_code = pair_code(l1, l2);
            if(m_literal_added.contains(index_code)){
                return;
            }
            var_table common_vars;
            get_common_vars(l1, l2, common_vars);
            for(var v: common_vars){
                nra_arith_var const * curr_arith = m_arith_vars[v];
                if(m_step <= curr_arith->get_tabu()){
                    continue;
                }
                interval_set_ref curr_st1(m_ism), curr_st2(m_ism);
                curr_st1 = m_evaluator.infeasible_intervals(l1->get_atom(), l1->sign(), nullptr, v);
                curr_st2 = m_evaluator.infeasible_intervals(l2->get_atom(), l2->sign(), nullptr, v);
                if(curr_arith->m_infeasible_st != nullptr){
                    m_ism.inc_ref(curr_arith->m_infeasible_st);
                }
                interval_set_ref union_st(m_ism);
                union_st = m_ism.mk_union(curr_st1, curr_st2, curr_arith->m_infeasible_st);
                if(m_ism.is_full(union_st)){
                    continue;
                }
                insert_in_complement_level1(v, union_st, index_code);
                insert_in_complement_level2(v, union_st, index_code);
            }
        }

        void get_common_vars(nra_literal const * l1, nra_literal const * l2, var_table & vars){
            vars.reset();
            for(var v: l1->m_vars){
                if(l2->m_vars.contains(v)){
                    vars.insert(v);
                }
            }
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
                if(curr_arith->m_infeasible_st != nullptr){
                    m_ism.inc_ref(curr_arith->m_infeasible_st);
                }
                interval_set_ref union_st(m_ism);
                union_st = m_ism.mk_union(curr_st, curr_arith->m_infeasible_st);
                if(m_ism.is_full(union_st)){
                    continue;
                }
                insert_in_complement_level1(v, union_st, l->get_index());
                insert_in_complement_level2(v, union_st, l->get_index());
            }
        }

        var pick_critical_nra_move(anum & best_value){
            TRACE("nlsat_ls2", tout << "start of pick nra move\n";
                show_ls_assignment(tout);
                // display_clause_weight(tout);
            );
            LSTRACE(tout << "show time of start picking nra move\n";
                TimeElapsed();
            );
            int best_arith_score;
            var best_arith_index;

            // Level 0.
            // consider pair literal operation in unsat clauses
            if(m_pair_cm == 1){
                LSTRACE(tout << "LEVEL 0: consider pair literals in unsat clauses\n";);
                reset_arith_operation();
                SASSERT(m_unsat_clauses.empty());
                // loop all unsat clauses, add pair literals
                for(unsigned i = 0; i < m_unsat_clauses.size(); i++){
                    nra_clause const * cls1 = m_nra_clauses[i];
                    for(unsigned j = i + 1; j < m_unsat_clauses.size(); j++){
                        nra_clause const * cls2 = m_nra_clauses[j];
                        for(literal_index l1: cls1->m_arith_literals){
                            nra_literal const * lit1 = m_nra_literals[l1];
                            for(literal_index l2: cls2->m_arith_literals){
                                nra_literal const * lit2 = m_nra_literals[l2];
                                add_pair_literal_arith_operation(lit1, lit2);
                            }
                        }
                    }
                }
                LSTRACE(display_arith_operations_level1(tout););
                literal_index best_literal_index;
                best_arith_score = 1;
                best_arith_index = select_best_from_arith_operations_level1(best_arith_score, best_value, best_literal_index);
                // var best_arith_index_level1 = select_best_from_arith_operations(INT_MIN, best_value_level1, best_literal_index_level1);
                // untabu decreasing arith variable exists
                if(best_arith_index != null_var){
                    LSTRACE(
                        tout << "LEVEL 0: choose var " << best_arith_index << std::endl;
                        tout << "show value: "; m_am.display(tout, best_value); tout << std::endl;
                        tout << "best literal index: " << best_literal_index << std::endl;
                    );
                    LSTRACE(tout << "show time of end picking nra move\n";
                        TimeElapsed();
                    );
                    return best_arith_index;
                }
                best_arith_score = 1;
                best_arith_index = select_best_from_arith_operations_level2(best_arith_score, best_value, best_literal_index);
                if(best_arith_index != null_var) {
                    LSTRACE(
                        tout << "LEVEL 0.5: choose var " << best_arith_index << std::endl;
                        tout << "show value: "; m_am.display(tout, best_value); tout << std::endl;
                        tout << "best literal index: " << best_literal_index << std::endl;
                    );
                    LSTRACE(tout << "show time of end picking nra move\n";
                        TimeElapsed();
                    );
                    return best_arith_index;
                }
            }

            // Level I.
            // consider literal in unsat clauses
            // add bounded interval set
            reset_arith_operation();
            LSTRACE(tout << "LEVEL I: consider literals in unsat clauses\n";);
            SASSERT(!m_unsat_clauses.empty());
            TRACE("nlsat_ls2", tout << "number of unsat clauses: " << m_unsat_clauses.size() << "\n");
            int unsat_idx = rand_int() % m_unsat_clauses.size();
            int cls_idx = m_unsat_clauses[unsat_idx];
            nra_clause const * curr_clause = m_nra_clauses[cls_idx];
            TRACE("nlsat_ls2", tout << "consider clause: "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
            for(literal_index lit_idx: curr_clause->m_arith_literals){
                nra_literal const * curr_literal = m_nra_literals[lit_idx];
                add_literal_arith_operation(curr_literal);
            }

            // loop operation arith variables
            LSTRACE(display_arith_operations_level1(tout););
            literal_index best_literal_index;
            // anum best_value_level1;
            best_arith_score = 1;
            best_arith_index = select_best_from_arith_operations_level1(best_arith_score, best_value, best_literal_index);
            // var best_arith_index_level1 = select_best_from_arith_operations(INT_MIN, best_value_level1, best_literal_index_level1);
            // untabu decreasing arith variable exists
            if(best_arith_index != null_var){
                LSTRACE(
                    tout << "LEVEL I: choose var " << best_arith_index << std::endl;
                    tout << "show value: "; m_am.display(tout, best_value); tout << std::endl;
                    tout << "best literal index: " << best_literal_index << std::endl;
                );
                LSTRACE(tout << "show time of end picking nra move\n";
                    TimeElapsed();
                );
                return best_arith_index;
            }
            LSTRACE(tout << "LEVEL I stuck\n";);
/*
            best_arith_score = 1;
            best_arith_index = select_best_from_arith_operations_level2(best_arith_score, best_value, best_literal_index);
            if(best_arith_index != null_var) {
                LSTRACE(
                    tout << "LEVEL 1.5: choose var " << best_arith_index << std::endl;
                    tout << "show value: "; m_am.display(tout, best_value); tout << std::endl;
                    tout << "best literal index: " << best_literal_index << std::endl;
                );
                LSTRACE(tout << "show time of end picking nra move\n";
                    TimeElapsed();
                );
                return best_arith_index;
            }
*/
            // Level 1.5
            // consider insertion sample values of level2.

            // Level II.
            // consider sat clause with false literals
            // var best_arith_index_level2;
            // literal_index best_literal_index_level2;
            // anum best_value_level2;
            /*
            LSTRACE(tout << "Level II: consider literals in sat clause\n";);
            if(!m_sat_clause_with_false_literals.empty()){
                reset_arith_operation();
                add_swap_operation();
                best_arith_score = 1;
                best_arith_index = select_best_from_arith_operations_level1(best_arith_score, best_value, best_literal_index);
                // best_arith_index_level2 = select_best_from_arith_operations(INT_MIN, best_value_level2, best_literal_index_level2);
                if(best_arith_index != null_var){
                    LSTRACE(
                        tout << "LEVEL II: choose var " << best_arith_index << std::endl;
                        tout << "show value: "; m_am.display(tout, best_value); tout << std::endl;
                        tout << "best literal index: " << best_literal_index << std::endl;
                    );
                    LSTRACE(tout << "show time of end picking nra move\n";
                        TimeElapsed();
                    );
                    return best_arith_index;
                }
                best_arith_score = 1;
                best_arith_index = select_best_from_arith_operations_level2(best_arith_score, best_value, best_literal_index);
                if(best_arith_index != null_var) {
                    LSTRACE(
                        tout << "LEVEL 2.5: choose var " << best_arith_index << std::endl;
                        tout << "show value: "; m_am.display(tout, best_value); tout << std::endl;
                        tout << "best literal index: " << best_literal_index << std::endl;
                    );
                    LSTRACE(tout << "show time of end picking nra move\n";
                        TimeElapsed();
                    );
                    return best_arith_index;
                }
            }
            LSTRACE(tout << "LEVEL II stuck\n";);
            */

            // update clause weight
            if(rand_int() % 10000 > smooth_probability){
                update_clause_weight();
            }
            else {
                smooth_clause_weight();
            }

            if (m_nra_operation_index_level1.size() > 0) {
                unsigned rand_index = rand_int() % (m_nra_operation_index_level1.size());
                return m_nra_operation_index_level1[rand_index];
            }

            // random_walk();
            LSTRACE(tout << "end of pick nra move\n";);
            LSTRACE(tout << "show time of end picking nra move\n";
                TimeElapsed();
            );
            return null_var;
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

        void reset_arith_operation(){
            m_nra_operation_index_level1.reset();
            m_nra_operation_value_level1.reset();
            m_nra_operation_literal_index_level1.reset();
            m_literal_added.reset();

            m_nra_operation_index_level2.reset();
            m_nra_operation_value_level2.reset();
            m_nra_operation_literal_index_level2.reset();
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
                        res_score += curr_clause->get_weight();
                    }
                    // sat --> unsat
                    else if(before_sat_count > 0 && after_sat_count == 0){
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
            TRACE("nlsat_ls2", tout << "start of critical nra move\n";
                tout << "var: " << v << std::endl;
                tout << "value: "; m_am.display(tout, old_value);
                tout << "->";
                m_am.display(tout, value); tout << std::endl;
                display_unsat_clauses(tout);
            );
            LSTRACE(show_ls_assignment(tout););
            m_assignment.set(v, value);

            critical_subscore_nra(v, value);
            // update arith score
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
            for(clause_index idx: m_unsat_clauses){
                nra_clause * cls = m_nra_clauses[idx];
                cls->inc_weight();
                // increase bool score for unsat clauses (because we increase weight for clause)
                for(literal_index lit_idx: cls->m_bool_literals){
                    nra_literal const * curr_literal = m_nra_literals[lit_idx];
                    nra_bool_var * curr_bool = m_bool_vars[curr_literal->get_bool_index()];
                    curr_bool->inc_score();
                }
            }
            m_total_clause_weight += m_unsat_clauses.size();
            LSTRACE(display_clause_weight(tout););
        }

        void smooth_clause_weight(){
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
            }
        }

        /**
         * Random Walk
         */
        void random_walk(){
            SASSERT(!m_unsat_clauses.empty());
            TRACE("nlsat_ls2", tout << "start of random walk\n";);
            reset_arith_operation();
            m_bool_operation_index.reset();
            
            // intsert operations
            for(unsigned i = 0; i < 3 && m_bool_operation_index.size() + m_nra_operation_index_level1.size() + m_nra_operation_index_level2.size() < 5; i++){
                clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
                nra_clause const * curr_clause = m_nra_clauses[c_idx];
                LSTRACE(tout << "consider clause "; m_solver.display(tout, *curr_clause->get_clause()); tout << std::endl;);
                // LSTRACE(display_var_set(tout, curr_clause->m_arith_literals));
                // loop arith literals
                for(literal_index l_idx: curr_clause->m_arith_literals){
                    nra_literal const * curr_literal = m_nra_literals[l_idx];
                    add_literal_arith_operation(curr_literal);   
                }
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
            LSTRACE(tout << "[debug] nra size: " << m_nra_operation_index_level1.size() + m_nra_operation_index_level2.size() << std::endl;
                display_arith_operations(tout);
            );
            LSCTRACE(m_nra_operation_index_level1.empty() && m_nra_operation_index_level2.empty() && m_bool_operation_index.empty(), tout << "stuck in random walk operation\n";);

            // make move
            if(m_bool_operation_index.size() + m_nra_operation_index_level1.size() + m_nra_operation_index_level2.size() == 0){
                LSTRACE(tout << "empty operation, return\n";
                    show_ls_assignment(tout);
                );
                m_stuck++;
                m_stuck_ratio = 1.0 * m_stuck / m_step;
                no_operation_random_walk();
                return;
            }
            // arith move
            if(m_bool_operation_index.empty() || (m_bool_operation_index.size() > 0 && m_nra_operation_index_level1.size() + m_nra_operation_index_level2.size() > 0 && !is_bool_search)){
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
            TRACE("nlsat_ls2", tout << "Perform no_operation_random_walk\n";);
            SASSERT(!m_unsat_clauses.empty());
            clause_index c_idx = m_unsat_clauses[rand_int() % m_unsat_clauses.size()];
            nra_clause const * cls = m_nra_clauses[c_idx];
            SASSERT(cls->size() != 0);
            literal_index l_idx = cls->m_literals[rand_int() % cls->size()];
            nra_literal const * lit = m_nra_literals[l_idx];
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
                TRACE("nlsat_ls2", tout << "m_var_value_fixed[picked_v] = " << m_var_value_fixed[picked_v] << std::endl;);
                if(m_var_value_fixed[picked_v]){
                    m_ism.peek_in_complement(old_value_interval, false, w, true);
                }
                else {
                    interval_set_ref curr_st(m_ism);
                    if(curr_arith->m_infeasible_st != nullptr){
                        m_ism.inc_ref(curr_arith->m_infeasible_st);
                    }
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
                        TRACE("nlsat_ls2", tout << "curr_st = " << curr_st << std::endl;);
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

        // v is the arith var we need to move
        bool cad_move(nra_literal const * l, var & picked_v, anum & w){
            TRACE("nlsat_ls2", tout << "perform cad_move\n";);
            var before_var = picked_v;
            LSTRACE(tout << "enter cad move\n";
                tout << "var: " << picked_v << std::endl;
            );
            if(l->m_vars.size() <= 1){
                return false;
            }
            m_cad_move++;

            poly const * p = get_atom_polys(l->get_atom());
            var x = lowest_degree_var(l, p);
            picked_v = lowest_degree_var_except(l, p, x);
            SASSERT(picked_v != x && picked_v != null_var);
            LSTRACE(tout << "lowest var: " << x << std::endl;);
            SASSERT(x != null_var);
            std::chrono::steady_clock::time_point m_before_projection = std::chrono::steady_clock::now();
            polynomial_ref_vector project_polys(m_pm);
            add_lc(p, x, project_polys);
            std::chrono::steady_clock::time_point m_after_lc = std::chrono::steady_clock::now();
            std::chrono::duration<double> dura1 = m_after_lc - m_before_projection;
            LSTRACE(tout << "time of add lc: " << dura1.count() << " s\n";
                std::cout << "time of add lc: " << dura1.count() << " s\n";
            );
            // level I. change value with leading coefficients
            LSTRACE(tout << "after adding lc\n";);
            LSTRACE(display_poly_vector(tout, project_polys));
            simplify(project_polys, picked_v);
            anum_vector roots_level1;
            get_cell_infos(project_polys, picked_v, roots_level1);
            LSTRACE(tout << "after adding lc, show roots in level1:\n";
                display_anum_vector(tout, roots_level1);
            );
            remove_duplicate(roots_level1);
            unsigned cell_num_level1 = 2 * roots_level1.size() + 1;
            if(cell_num_level1 > 1){
                unsigned curr_index = find_cell_index(roots_level1, m_assignment.value(picked_v));
                LSTRACE(tout << "curr index: " << curr_index << std::endl;);
                anum old_value;
                m_am.set(old_value, m_assignment.value(picked_v));
                if(cell_num_level1 <= 9){
                    for(unsigned i = 0; i < cell_num_level1; i++){
                        if(i == curr_index){
                            continue;
                        }
                        LSTRACE(tout << "show index: " << i << std::endl;);
                        anum sample_value;
                        choose_sample(roots_level1, i, sample_value);
                        LSTRACE(tout << "show sample: "; m_am.display(tout, sample_value); tout << std::endl;);
                        m_assignment.set(picked_v, sample_value);
                        if(!is_literal_stuck(l)){
                            LSTRACE(tout << "cad succeed\n";);
                            // restore assignment
                            m_assignment.set(picked_v, old_value);
                            m_am.set(w, sample_value);
                            m_cad_succeed++;
                            return true;   
                        }
                        LSTRACE(tout << "cad failed\n";);
                    }
                    // restore assignment
                    m_assignment.set(picked_v, old_value);
                }
                // random choose 9
                else {
                    var_vector idx_vec;
                    for(unsigned i = 0; i < cell_num_level1; i++){
                        idx_vec.push_back(i);
                    }
                    var_vector choice_vec;
                    random_choose(idx_vec, 9, choice_vec);
                    SASSERT(choice_vec.size() == 9);
                    for(unsigned i = 0; i < choice_vec.size(); i++){
                        if(choice_vec[i] == curr_index){
                            continue;
                        }
                        LSTRACE(tout << "show index: " << choice_vec[i] << std::endl;);
                        anum sample_value;
                        choose_sample(roots_level1, choice_vec[i], sample_value);
                        LSTRACE(tout << "show sample: "; m_am.display(tout, sample_value); tout << std::endl;);
                        m_assignment.set(picked_v, sample_value);
                        if(!is_literal_stuck(l)){
                            LSTRACE(tout << "cad succeed\n";);
                            // restore assignment
                            m_assignment.set(picked_v, old_value);
                            m_am.set(w, sample_value);
                            m_cad_succeed++;
                            return true;   
                        }
                        LSTRACE(tout << "cad failed\n";);
                    }
                    // restore assignment
                    m_assignment.set(picked_v, old_value);
                }
            }
            LSTRACE(tout << "levelI failed, enter levelII\n";);


            add_discriminant(p, x, project_polys);
            std::chrono::steady_clock::time_point m_after_projection = std::chrono::steady_clock::now();
            std::chrono::duration<double> dura = m_after_projection - m_before_projection;
            LSTRACE(tout << "time of projection: " << dura.count() << " s\n";
                std::cout << "time of projection: " << dura.count() << " s\n";
            );
            LSTRACE(tout << "after projection\n";);
            LSTRACE(display_poly_vector(tout, project_polys));
            // only save polynomials which have v
            simplify(project_polys, picked_v);
            LSTRACE(tout << "after simplify\n";);
            LSTRACE(display_poly_vector(tout, project_polys));
            anum_vector roots;
            get_cell_infos(project_polys, picked_v, roots);
            LSTRACE(tout << "after get cell infos\n";);
            LSTRACE(tout << "show roots:\n";
                display_anum_vector(tout, roots);
            );
            remove_duplicate(roots);
            unsigned cell_num = 2 * roots.size() + 1;
            LSTRACE(tout << "show cell num: " << cell_num << std::endl;);
            LSTRACE(tout << "show roots:\n";
                display_anum_vector(tout, roots);
            );
            if(cell_num == 1){
                LSTRACE(tout << "cell num is one, cad fail\n";);
                // restore var
                picked_v = before_var;
                return false;
            }
            unsigned curr_index = find_cell_index(roots, m_assignment.value(picked_v));
            LSTRACE(tout << "curr index: " << curr_index << std::endl;);
            anum old_value;
            m_am.set(old_value, m_assignment.value(picked_v));
            if(cell_num <= 9){
                for(unsigned i = 0; i < cell_num; i++){
                    if(i == curr_index){
                        continue;
                    }
                    LSTRACE(tout << "show index: " << i << std::endl;);
                    anum sample_value;
                    choose_sample(roots, i, sample_value);
                    LSTRACE(tout << "show sample: "; m_am.display(tout, sample_value); tout << std::endl;);
                    m_assignment.set(picked_v, sample_value);
                    if(!is_literal_stuck(l)){
                        LSTRACE(tout << "cad succeed\n";);
                        m_assignment.set(picked_v, old_value);
                        m_am.set(w, sample_value);
                        m_cad_succeed++;
                        return true;   
                    }
                    LSTRACE(tout << "cad failed\n";);
                }
                m_assignment.set(picked_v, old_value);
                // restore var
                picked_v = before_var;
                return false;
            }
            // random choose 9
            else {
                var_vector idx_vec;
                for(unsigned i = 0; i < cell_num; i++){
                    idx_vec.push_back(i);
                }
                var_vector choice_vec;
                random_choose(idx_vec, 9, choice_vec);
                SASSERT(choice_vec.size() == 9);
                for(unsigned i = 0; i < choice_vec.size(); i++){
                    if(choice_vec[i] == curr_index){
                        continue;
                    }
                    LSTRACE(tout << "show index: " << choice_vec[i] << std::endl;);
                    anum sample_value;
                    choose_sample(roots, choice_vec[i], sample_value);
                    LSTRACE(tout << "show sample: "; m_am.display(tout, sample_value); tout << std::endl;);
                    m_assignment.set(picked_v, sample_value);
                    if(!is_literal_stuck(l)){
                        LSTRACE(tout << "cad succeed\n";);
                        m_assignment.set(picked_v, old_value);
                        m_am.set(w, sample_value);
                        m_cad_succeed++;
                        return true;   
                    }
                    LSTRACE(tout << "cad failed\n";);
                }
                // restore var
                picked_v = before_var;
                m_assignment.set(picked_v, old_value);
                return false;
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

        void get_cell_infos(polynomial_ref_vector const & ps, var v, anum_vector & vec){
            vec.reset();
            polynomial_ref p(m_pm);
            for(unsigned i = 0; i < ps.size(); i++){
                p = ps.get(i);
                LSTRACE(tout << "show curr poly:\n";
                    m_pm.display(tout, p); tout << std::endl;
                );
                anum_vector curr;
                m_am.isolate_roots(p, undef_var_assignment(m_assignment, v), curr);
                LSTRACE(display_anum_vector(tout, curr););
                for(auto ele: curr){
                    if(!contains_value(vec, ele)){
                        vec.push_back(ele);
                    }
                }
            }
            anum_heap_sort(vec);
        }

        void shiftdown(anum_vector & vec, int n, int i){
            int k = i;
            while(2 * k + 1 < n){
                int j = 2 * k + 1;
                if((j+1<n) && m_am.lt(vec[j], vec[j+1])){
                    j++;
                }
                if(m_am.lt(vec[k], vec[j])){
                    m_am.swap(vec[k], vec[j]);
                    k = j;
                    continue;
                }
                break;
            }
        }

        void anum_heap_sort(anum_vector & vec){
            LSTRACE(tout << "before sort:\n";
                display_anum_vector(tout, vec);
            );
            int n = vec.size();
            for(int i = (n-1)/2; i >= 0; i--){
                shiftdown(vec, n, i);
            }
            for(int i = n-1; i > 0; i--){
                m_am.swap(vec[0], vec[i]);
                shiftdown(vec, i, 0);
            }
            LSTRACE(tout << "after sort:\n";
                display_anum_vector(tout, vec);
            );
        }

        void simplify(polynomial_ref_vector & res, var v){
            polynomial_ref curr(m_pm);
            unsigned j = 0;
            for(unsigned i = 0; i < res.size(); i++){
                curr = res.get(i);
                var_vector vars;
                m_pm.vars(curr, vars);
                if(vars.contains(v)){
                    res[j++] = curr;
                }
            }
            res.shrink(j);
        }


        void add_lc(poly const * p, var x, polynomial_ref_vector & res){
            unsigned k = m_pm.degree(p, x);
            SASSERT(k > 0);
            if(m_pm.nonzero_const_coeff(p, x, k)){
                return;
            }
            while(true){
                polynomial_ref lc(m_pm);
                lc = m_pm.coeff(p, x, k);
                add_factors(lc, res);
                if(!is_zero(lc) && ::is_zero(m_am.eval_sign_at(lc, m_assignment))){
                    break;
                }
                if(k == 0){
                    break;
                }
                k--;
            }
        }

        void add_discriminant(poly const * p, var x, polynomial_ref_vector & res){
            if(m_pm.degree(p, x) < 2){
                return;
            }
            polynomial_ref p_prime(m_pm);
            p_prime = m_pm.derivative(p, x);
            polynomial_ref_vector temp(m_pm);
            std::chrono::steady_clock::time_point m_before_psc = std::chrono::steady_clock::now();
            psc_chain(p, p_prime, x, temp);
            std::chrono::steady_clock::time_point m_after_psc = std::chrono::steady_clock::now();
            std::chrono::duration<double> psc_dura = m_after_psc - m_before_psc;
            LSTRACE(tout << "time of psc: " << psc_dura.count() << " s\n";
                std::cout << "time of psc: " << psc_dura.count() << " s\n";
            );
            polynomial_ref curr(m_pm);
            for(unsigned i = 0; i < temp.size(); i++){
                curr = temp.get(i);
                if(is_zero(curr) || is_const(curr) || is_zero(m_am.eval_sign_at(curr, m_assignment))){
                    LSTRACE(tout << "continue\n";);
                    continue;
                }
                LSTRACE(tout << "here\n";
                    std::cout << "here\n";
                );
                std::chrono::steady_clock::time_point m_before_factor = std::chrono::steady_clock::now();
                add_factors(curr, res);
                std::chrono::steady_clock::time_point m_after_factor = std::chrono::steady_clock::now();
                std::chrono::duration<double> factor_dura = m_after_factor - m_before_factor;
                LSTRACE(tout << "time of factor: " << factor_dura.count() << " s\n";
                    std::cout << "time of factor: " << factor_dura.count() << " s\n";
                );
            }
        }

        void psc_chain(poly const * p, polynomial_ref & q, var x, polynomial_ref_vector & res){
            m_cache.psc_chain(p, q, x, res);
        }

        void add_factors(polynomial_ref const & p, polynomial_ref_vector & res){
            if(is_const(p)){
                return;
            }
            if(use_factor){
                temp_factors.reset();
                m_cache.factor(p, temp_factors);
                polynomial_ref f(m_pm);
                for(unsigned i = 0; i < temp_factors.size(); i++){
                    f = temp_factors.get(i);
                    if(!is_const(f)){
                        res.push_back(f);
                    }
                }
            }
            else {
                res.push_back(p);
            }
        }

        var lowest_degree_var_except(nra_literal const * l, poly const * p, var x) const { 
            SASSERT(l->m_vars.size() >= 2);           
            unsigned min_degree = UINT_MAX;
            var res = null_var;
            for(var v: l->m_vars){
                if(v == x){
                    continue;
                }
                unsigned curr_degree = m_pm.degree(p, v);
                if(curr_degree < min_degree){
                    min_degree = curr_degree;
                    res = v;
                }
            }
            return res;
        }

        var lowest_degree_var(nra_literal const * l, poly const * p) const {
            unsigned min_degree = UINT_MAX;
            var res = null_var;
            for(var v: l->m_vars){
                unsigned curr_degree = m_pm.degree(p, v);
                if(curr_degree < min_degree){
                    min_degree = curr_degree;
                    res = v;
                }
            }
            return res;
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
                if(curr_var->m_infeasible_st != nullptr){
                    m_ism.inc_ref(curr_var->m_infeasible_st);
                }
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
                for(unsigned i = 0; m_nra_operation_index_level1.size() + m_nra_operation_index_level2.size() < 20 && i < 50; i++){
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

        /**
         * Local Search
         */
        local_search_result local_search(){
            enable_trace("nlsat_ls_stat");
            TRACE("nlsat_ls2", tout << "max_step = " << max_step << std::endl;);
            TRACE("nlsat_ls2", tout << "m_pair_cm = " << m_pair_cm << std::endl;);
            SPLIT_LINE(tout);
            LSTRACE(tout << "local search begin\n";
                std::cout << "local search begin\n";
            );
            SPLIT_LINE(tout);
            no_improve_cnt = 0;
            m_start_time = std::chrono::steady_clock::now();
            m_step = 0;
            // ICP returns false
            if(!init_solution(true)){
                LSTRACE(std::cout << "ICP returns false\n";);
                LSTRACE(tout << "ICP returns false\n";);
                m_bool_result.reset();
                return std::make_pair(l_false, m_bool_result);
            }
            m_outer_step = 1;
            for(m_step = 1; m_step < max_step; m_step++){
                if (m_step % 100 == 0) {
                    std::cout << m_step << std::endl;
                }
                m_stuck_ratio = 1.0 * m_stuck / m_step;
                LSTRACE(tout << "step: " << m_step << std::endl;
                    tout << "no improve cnt: " << no_improve_cnt << std::endl;
                );
                // Succeed
                if(m_unsat_clauses.empty()){
                    SPLIT_LINE(std::cout);
                    TRACE("nlsat_ls_stat",
                        std::cout << "local search succeed\n";
                        tout << "local search succeed\n";
                    );
                    SPLIT_LINE(std::cout);
                    
                    collect_bool_values();
                    check_solution_sat();
                    propagate_sub_values();
                    return std::make_pair(l_true, m_bool_result);
                }
                // Fail
                if(TimeElapsed() > m_cutoff && m_step % 100 == 0){
                    SPLIT_LINE(std::cout);
                    LSTRACE(std::cout << "local search failed\n";);
                    SPLIT_LINE(std::cout);

                    m_bool_result.reset();
                    return std::make_pair(l_undef, m_bool_result);
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
                if(rand_int() % 2 == 0){
                    // pick bool variable
                    bool_var picked_b = pick_critical_bool_move();
                    LSTRACE(tout << "picked bool var: " << picked_b << std::endl;);
                    if(picked_b != null_var){
                        critical_bool_move(picked_b);
                    }
                    // update bool improvement
                    if(update_bool_info()){
                        no_improve_cnt_bool = 0;
                    }
                    else {
                        no_improve_cnt_bool++;
                    }
                }
                else {
                    // pick arith variable and next value
                    scoped_anum next_value(m_am);
                    var picked_v = pick_critical_nra_move(next_value);
                    CTRACE("nlsat_ls_stat", m_step % 100 == 0, tout << "picked arith var: " << picked_v << std::endl;
                            tout << "picked arith value: "; m_am.display(tout, next_value); tout << std::endl;
                    );
                    if(picked_v != null_var){
                        critical_nra_move(picked_v, next_value);
                    }
                    // update arith improvement
                    if(update_nra_info()){
                        no_improve_cnt_nra = 0;
                    }
                    else {
                        no_improve_cnt_nra++;
                    }
                }
                CTRACE("nlsat_ls_stat", m_step % 100 == 0,
                    tout << "number of unsatisfied clauses: " << m_unsat_clauses.size() << std::endl;);
                // update improvement
                if(update_solution_info()){
                    no_improve_cnt = 0;
                }
                else {
                    no_improve_cnt++;
                }

                // Restart
                // if(no_improve_cnt > 500000){
                if(no_improve_cnt > 10000){
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
                }
            }
            m_bool_result.reset();
            SPLIT_LINE(std::cout);
            LSTRACE(std::cout << "local search failed\n";);
            SPLIT_LINE(std::cout);
            return std::make_pair(l_undef, m_bool_result);
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
            m_am.display(out << "m_max: ", m_max) << std::endl;
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
            display_arith_operations_level1(out);
            display_arith_operations_level2(out);
            return out;
        }

        std::ostream & display_arith_operations_level1(std::ostream & out) const {
            out << "show arith operations\n";
            SASSERT(m_nra_operation_index_level1.size() == m_nra_operation_value_level1.size());
            if(m_nra_operation_index_level1.empty()){
                out << "operation is empty\n";
                show_ls_assignment(out);
            }
            for(unsigned i = 0; i < m_nra_operation_index_level1.size(); i++){
                out << "var: " << m_nra_operation_index_level1[i] << "  ";
                out << "value: "; m_am.display(out, m_nra_operation_value_level1[i]);
                out << std::endl;
            }
            return out;
        }

        std::ostream & display_arith_operations_level2(std::ostream & out) const {
            out << "show arith operations\n";
            SASSERT(m_nra_operation_index_level2.size() == m_nra_operation_value_level2.size());
            if(m_nra_operation_index_level2.empty()){
                out << "operation is empty\n";
                show_ls_assignment(out);
            }
            for(unsigned i = 0; i < m_nra_operation_index_level2.size(); i++){
                out << "var: " << m_nra_operation_index_level2[i] << "  ";
                out << "value: "; m_am.display(out, m_nra_operation_value_level2[i]);
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

        std::ostream & display_poly_bound_state(std::ostream & out, poly_bound_state s) const {
            switch(s){
                case EQ:
                    out << "==\n";
                    break;
                case NEQ:
                    out << "!=\n";
                    break;
                case GT:
                    out << ">\n";
                    break;
                case GE:
                    out << ">=\n";
                    break;
                case LT:
                    out << "<\n";
                    break;
                case LE:
                    out << "<=\n";
                    break;
                default:
                    UNREACHABLE();
            }
            return out;
        }
    };

    ls_helper::ls_helper(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, clause_vector const & cls, atom_vector const & ats, bool_vector const & dead, unsigned seed, unsigned & step, 
                         unsigned & stuck, double & ratio, unsigned & cad_move, unsigned & cad_succeed, unsigned & poly_bound, unsigned & pair_cm, 
                         substitute_value_vector const & vec
                         ){
        m_imp = alloc(imp, s, am, pm, cache, ism, ev, ass, cls, ats, dead, seed, step, stuck, ratio, cad_move, cad_succeed, poly_bound, pair_cm, vec);
    }

    ls_helper::~ls_helper(){
        dealloc(m_imp);
    }

    void ls_helper::set_var_num(unsigned x){
        m_imp->set_var_num(x);
    }

    local_search_result ls_helper::local_search(){
        return m_imp->local_search();
    }
};