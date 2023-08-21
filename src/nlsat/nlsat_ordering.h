#pragma once

namespace nlsat {
    #define                                                 UNIFORM_VSIDS                          1
    #define                                                 BOOL_FIRST_VSIDS                       2
    #define                                                 THEORY_FIRST_VSIDS                     3
    #define                                                 ORIGIN_STATIC_BOOL_FIRST_MODE          4
    #define                                                 RANDOM_MODE                            5
    
    #define DYNAMIC_MODE                                    UNIFORM_VSIDS
    
    struct uniform_vsids {
        const double_vector & m_activity;
        uniform_vsids(double_vector const & vec): m_activity(vec) {}
        bool operator()(hybrid_var v1, hybrid_var v2) const {
            return m_activity[v1] == m_activity[v2] ? v1 < v2 : m_activity[v1] > m_activity[v2];
        }
    };

    struct bool_first_vsids {
        const double_vector & m_activity;
        const unsigned & m_num_bool;
        bool_first_vsids(double_vector const & vec, unsigned const & num_bool): m_activity(vec), m_num_bool(num_bool) {}
        bool operator()(hybrid_var v1, hybrid_var v2) const {
            // two bool vars
            if(v1 < m_num_bool && v2 < m_num_bool){
                return m_activity[v1] == m_activity[v2] ? v1 < v2 : m_activity[v1] > m_activity[v2];
            }
            // two arith vars
            else if(v1 >= m_num_bool && v2 >= m_num_bool){
                return m_activity[v1] == m_activity[v2] ? v1 < v2 : m_activity[v1] > m_activity[v2];
            }
            else {
                SASSERT((v1 < m_num_bool) != (v2 < m_num_bool));
                // if v1 is bool var, return true
                // else return false
                return v1 < m_num_bool;
            }
        }
    };

    struct static_bool_first_order {
        const unsigned & m_num_bool;
        static_bool_first_order(unsigned const & num_bool): m_num_bool(num_bool) {}
        bool operator()(hybrid_var v1, hybrid_var v2) const {
            if(v1 < m_num_bool && v2 >= m_num_bool){
                return true;
            }
            else if(v1 >= m_num_bool && v2 < m_num_bool){
                return false;
            }
            else {
                return v1 < v2;
            }
        }
    };

    struct theory_first_vsids {
        const double_vector & m_activity;
        const unsigned & m_num_bool;
        theory_first_vsids(double_vector const & vec, unsigned const & num_bool): m_activity(vec), m_num_bool(num_bool) {}
        bool operator()(hybrid_var v1, hybrid_var v2) const {
            // two bool vars
            if(v1 < m_num_bool && v2 < m_num_bool){
                return m_activity[v1] == m_activity[v2] ? v1 < v2 : m_activity[v1] > m_activity[v2];
            }
            // two arith vars
            else if(v1 >= m_num_bool && v2 >= m_num_bool){
                return m_activity[v1] == m_activity[v2] ? v1 < v2 : m_activity[v1] > m_activity[v2];
            }
            else {
                SASSERT((v1 < m_num_bool) != (v2 < m_num_bool));
                // if v1 is theory var, return true
                // else return false
                return v1 >= m_num_bool;
            }
        }
    };
    
    struct random_order {
        unsigned m_seed;
        random_order(unsigned seed): m_seed(seed) {}
        bool operator()(hybrid_var v1, hybrid_var v2) const {
            random_gen r(m_seed);
            return r() % 2 == 0;
        }
    };
};