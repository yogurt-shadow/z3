#pragma once

#include <cstdio>
#include <chrono>
#include <string.h>
#include <stack>
#include <random>
#include <map>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdlib>
#include <exception>
#include <time.h>
#include <signal.h>
#include <unistd.h>
#include <sys/types.h>
#include <string>
#include "nlsat/nlsat_scoped_literal_vector.h"
#include "math/polynomial/polynomial_cache.h"
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat/nlsat_clause.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_interval_set.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_interval_set.h"
#include "util/hashtable.h"

#define LSTRACE(CODE) TRACE("nlsat_ls", CODE)
#define LSCTRACE(COND, CODE) CTRACE("nlsat_ls", COND, CODE)
#define SPLIT_LINE(T) TRACE("nlsat_ls", T << "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";)

namespace nlsat {
    using literal_index = var;
    using clause_index = var;
    using var_pair = std::pair<var, var>;
    using poly_vector = vector<poly *>;
    using int_vector = vector<int>;

    struct var_hash {
        unsigned operator()(var v) const {
            return v;
        }
    };

    struct var_eq {
        bool operator()(var x, var y) const {
            return x == y;
        }
    };

    using var_table =  hashtable<var, var_hash, var_eq>;
    using literal_index_table = var_table;
    using clause_index_table = var_table;

    class bool_operation_table {
    private:
        unsigned & num_vars;
        var_vector & m_bools;
        bool_vector & m_chosen;

    public:
        bool_operation_table(var_vector & bools, bool_vector & chosen, unsigned & num)
        : m_bools(bools), m_chosen(chosen), num_vars(num)
        {}

        ~bool_operation_table(){}

        void reset() {
            m_bools.reset();
            m_chosen.resize(num_vars, false);;
        }

        bool contains(bool_var b) const {
            return b < num_vars && m_chosen[b];
        }

        void insert(bool_var b) {
            SASSERT(b < num_vars);
            m_bools.push_back(b);
            m_chosen[b] = true;
        }
    };

    class arith_operation_table {
    private:
        anum_manager & m_am;
        var_vector & m_vars;
        anum_vector & m_values;
        var_vector & m_literals;
    public:
        arith_operation_table(anum_manager & am, var_vector & vec1, anum_vector & vec2, var_vector & vec3)
        : m_am(am), m_vars(vec1), m_values(vec2), m_literals(vec3)
        {}

        ~arith_operation_table(){}

        bool contains(var v, anum const & w) const {
            SASSERT(m_vars.size() == m_values.size());
            for(unsigned i = 0; i < m_vars.size(); i++){
                if(m_vars[i] == v && m_am.eq(m_values[i], w)){
                    return true;
                }
            }
            return false;
        }

        bool contains_literal(literal_index l_idx) const {
            return m_literals.contains(l_idx);
        }

        void reset() {
            m_vars.reset();
            m_values.reset();
            m_literals.reset();
        }

        unsigned size() const {
            return m_vars.size();
        }

        void insert_operation(var v, anum val, literal_index l_idx) {
            m_vars.push_back(v);
            m_values.push_back(val);
            m_literals.push_back(l_idx);
        }
    };

    // substitute var
    struct substitute_value {
        var m_var;
        poly const * p;
        poly const * q;
        substitute_value(var v, poly const * pp, poly const * qq): m_var(v), p(pp), q(qq) {}
    };

    using substitute_value_vector = vector<substitute_value>;

    // Literal
    class nra_literal {
    private:
        // literal index
        literal_index m_index;
        // bool or arith literal
        bool m_is_bool;
        // bool literal: convert[l.var()]
        // arith_literal: null_var
        bool_var m_bool_index;
        ineq_atom const * m_atom;
        bool m_is_sat;
        // count of critical nra move
        unsigned m_activity;
    public:
        const literal m_literal;
        var_table m_vars;
        // converted mult of polys (value of the atom)
        // sat: 0
        nra_literal(unsigned idx, unsigned b_idx, const literal l, bool is_bool, var_table const & vars, atom const * at)
        : m_index(idx), m_bool_index(b_idx), m_literal(l), m_is_bool(is_bool), m_vars(vars), m_atom(to_ineq_atom(at)), m_is_sat(false), 
        m_activity(0)
        {}

        bool is_bool() const {
            return m_is_bool;
        }

        bool is_arith() const {
            return !m_is_bool;
        }

        bool sign() const {
            return m_literal.sign();
        }

        unsigned get_activity() const {
            return m_activity;
        }

        void inc_activity(){
            m_activity++;
        }

        void set_activity(unsigned x){
            m_activity = x;
        }

        literal get_literal() const {
            return m_literal;
        }

        unsigned get_bool_index() const {
            SASSERT((m_is_bool && m_bool_index != null_var) || (!m_is_bool && m_bool_index == null_var));
            return m_bool_index;
        }

        var get_index() const {
            return m_index;
        }

        ineq_atom const * get_atom() const {
            return m_atom;
        }

        void set_sat_status(bool b){
            m_is_sat = b;
        }

        void flip_sat_status(){
            m_is_sat = !m_is_sat;
        }

        bool get_sat_status() const {
            return m_is_sat;
        }

        bool operator==(nra_literal other) const {
            return this->m_literal.sign() == other.m_literal.sign() && this->m_literal.var() == other.m_literal.var();
        }

        ~nra_literal(){}
    };

    using nra_literal_vector = ptr_vector<nra_literal>;

    // Clause
    class nra_clause {
    private:
        clause_index m_index;
        clause const * m_clause;
        // sat count: number of sat literals
        unsigned m_weight, m_sat_count;
        // sat count == 1: the sat literal index
        // otherwise: null_var
        unsigned m_critical_index;
        bool m_is_sat;
        // left vars to assign
        unsigned m_left_vars;

    public:
        var_table m_vars, m_bool_var;
        var_vector m_literals, m_arith_literals, m_bool_literals;
        nra_clause(unsigned idx, clause const * cls, nra_literal_vector const & vec, var_table const & vars, var_table const & vars2)
        : m_index(idx), m_clause(cls), m_weight(1), m_vars(vars), m_is_sat(false), m_bool_var(vars2), m_critical_index(null_var),
        m_left_vars(vars.size())
        {
            m_literals.reset();
            m_arith_literals.reset();
            m_bool_literals.reset();

            for(auto ele: vec){
                var idx = ele->get_index();
                m_literals.push_back(idx);
                if(ele->is_bool()){
                    m_bool_literals.push_back(idx);
                }
                else {
                    SASSERT(ele->is_arith());
                    m_arith_literals.push_back(idx);
                }
            }
        }

        clause const * get_clause() const {
            return m_clause;
        }

        unsigned size() const {
            return m_literals.size();
        }

        unsigned arith_size() const {
            return m_arith_literals.size();
        }

        unsigned bool_size() const {
            return m_bool_literals.size();
        }

        unsigned get_sat_count() const {
            return m_sat_count;
        }

        unsigned get_index() const {
            return m_index;
        }

        unsigned get_left_vars() const {
            return m_left_vars;
        }

        void dec_left_vars(var x){
            if(m_vars.contains(x)){
                SASSERT(m_left_vars > 0);
                m_left_vars--;
            }
        }

        void reset_left_vars(){
            m_left_vars = m_vars.size();
        }

        void set_sat_count(unsigned x){
            m_sat_count = x;
        }

        void set_sat_status(bool b){
            m_is_sat = b;
        }

        void inc_weight(){
            m_weight++;
        }

        void dec_weight(){
            m_weight--;
        }

        void set_critical_index(unsigned x){
            m_critical_index = x;
        }

        unsigned get_critical_index() const {
            return m_critical_index;
        }

        unsigned get_weight() const {
            return m_weight;
        }

        bool get_sat_status() const {
            return m_is_sat;
        }

        ~nra_clause(){}
    };

    using nra_clause_vector = ptr_vector<nra_clause>;

    // Arith Variable
    class nra_arith_var {
    private:
        var m_index;
        unsigned m_last_move, m_tabu;
        int m_score;
    public:
        // infeasible set of arith var
        interval_set * m_feasible_st;
        interval_set * m_infeasible_st;
        interval_set * m_init_st;
        // literals which contain this var
        var_vector m_literals;
        // the clause which the literal belongs to
        var_vector m_lit_cls;
        /**
         * The same literal may be contained in couple of clauses
         * In this case, we store copied version of literal
         * i.e.  literals: 1   1
         *       lit_cls:  2   3
         */
        // clauses which contain this var
        var_vector m_clauses;
        // st is initially full
        nra_arith_var(var idx, interval_set * st, interval_set * st2)
        : m_index(idx), m_last_move(0), m_tabu(0), m_score(0), m_feasible_st(st), m_infeasible_st(st2)
        {
            m_literals.reset();
            m_lit_cls.reset();
            m_clauses.reset();
            // m_poly_bound.reset();
        }

        void add_literal_clause(literal_index l, clause_index c){
            m_literals.push_back(l);
            m_lit_cls.push_back(c);
            SASSERT(m_literals.size() == m_lit_cls.size());
        }

        // void push_poly_bound(poly const * p, poly_bound_state s){
        //     m_poly_bound.push_back(poly_bound(p, s));
        // }

        void add_clause(clause_index c){
            m_clauses.push_back(c);
        }

        int get_score() const {
            return m_score;
        }

        void inc_score(){
            m_score++;
        }

        void dec_score(){
            m_score--;
        }

        void set_score(int x){
            m_score = x;
        }

        unsigned get_last_move() const {
            return m_last_move;
        }

        void set_last_move(unsigned x){
            m_last_move = x;
        }

        unsigned get_tabu() const {
            return m_tabu;
        }

        void set_tabu(unsigned x){
            m_tabu = x;
        }

        ~nra_arith_var(){}
    };

    // Bool Variable
    class nra_bool_var {
    private:
    /**
     * index means converted index (Continuous)
     * origin index means literal index (Discrete)
     */
        bool_var m_index;
        bool_var m_origin_index;
        bool m_value;
        unsigned m_last_move, m_tabu;
        int m_score;
    public:
        var_vector m_literals, m_lit_cls, m_clauses;
        nra_bool_var(bool_var idx, bool_var origin)
        : m_index(idx), m_origin_index(origin), m_value(true), m_score(0), m_tabu(0), m_last_move(0)
        {
            m_literals.reset();
            m_lit_cls.reset();
            m_clauses.reset();
        }

        void add_literal_clause(literal_index l, clause_index c){
            m_literals.push_back(l);
            m_lit_cls.push_back(c);
            SASSERT(m_literals.size() == m_lit_cls.size());
        }

        void add_clause(clause_index c){
            m_clauses.push_back(c);
        }
        
        // ^ pure bool index
        unsigned get_index() const {
            return m_index;
        }

        // ^ atom index
        unsigned get_origin_index() const {
            return m_origin_index;
        }

        void set_value(bool b){
            m_value = b;
        }

        bool get_value() const {
            return m_value;
        }

        int get_score() const {
            return m_score;
        }

        void inc_score(){
            m_score ++;
        }

        void dec_score(){
            m_score --;
        }

        void set_score(int x){
            m_score = x;
        }

        unsigned get_tabu() const {
            return m_tabu;
        }

        void set_tabu(unsigned x){
            m_tabu = x;
        }

        unsigned get_last_move() const {
            return m_last_move;
        }

        void set_last_move(unsigned x){
            m_last_move = x;
        }

        ~nra_bool_var(){}
    };

    typedef ptr_vector<nra_arith_var> nra_arith_var_vector;
    typedef ptr_vector<nra_bool_var> nra_bool_var_vector;

    class ls_helper {
    public:
        struct imp;
    private:
        imp * m_imp;
    public:
        ls_helper(solver & s, anum_manager & am, pmanager & pm, polynomial::cache & cache, interval_set_manager & ism, evaluator & ev, 
                         assignment & ass, svector<lbool> & bvalues, clause_vector const & cls, atom_vector const & ats, bool_var_vector const & pure_bool_vars, 
                         bool_var_vector const & pure_bool_convert, 
                        unsigned seed, unsigned & step, unsigned & stuck, double & ratio, substitute_value_vector const & vec);

        ~ls_helper();

        lbool local_search();

        void set_var_num(unsigned x);
    };

    /**
     * 2022/08/31
     * literal activity for critical move
     * add operation for top more literals
     */
    struct arith_literal_activity {
        const nra_literal_vector & m_nra_literals;
        arith_literal_activity(nra_literal_vector const & vec): m_nra_literals(vec) {}

        bool operator()(literal_index v1, literal_index v2) const {
            return m_nra_literals[v1]->get_activity() == m_nra_literals[v2]->get_activity() ? v1 < v2 : m_nra_literals[v1]->get_activity() > m_nra_literals[v2]->get_activity();
        }
    };
};