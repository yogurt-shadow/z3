#include "nlsat/nlsat_caching_system.h"

namespace nlsat {
    struct nlsat_caching_system::imp {
        interval_set_manager &        m_ism;
        atom_vector            const &m_atoms;
        clause_vector          const &m_clauses;
        unsigned                      num_vars;

        interval_set_vector    m_atom_caching_set;
        pmanager               & m_pm;
        bool_vector            m_atom_caching_enabled;
        // var -> atom
        vector<var_vector>     m_var_atoms;
        // atom -> vars
        vector<var_vector>     m_atom_vars;

        imp(interval_set_manager & ism, pmanager & pm, atom_vector const &ats, clause_vector const &cls): m_ism(ism), m_pm(pm), m_atoms(ats), m_clauses(cls) 
        {
            // std::cout << "init imp done" << std::endl;
        }

        void clear() {
            m_atom_caching_enabled.clear();
            m_atom_caching_set.clear();
            m_atom_caching_enabled.resize(m_atoms.size(), false);
            m_atom_caching_set.resize(m_atoms.size(), nullptr);
            m_var_atoms.clear();
            m_var_atoms.resize(num_vars, var_vector());
            m_atom_vars.clear();
            collect_var_atoms();
        }

        void init_vars(unsigned x) {
            num_vars = x;
        }

        void collect_atom_vars(atom const *a, var_vector &vec) {
            vec.clear();
            if(a->is_root_atom()) {
                m_pm.vars(to_root_atom(a)->p(), vec);
            } else {
                for(unsigned j = 0; j < to_ineq_atom(a)->size(); j++) {
                    var_vector vec2;
                    m_pm.vars(to_ineq_atom(a)->p(j), vec2);
                    for(var v: vec2) {
                        if(!vec.contains(v)) {
                            vec.push_back(v);
                        }
                    }
                }
            }
        }

        void collect_var_atoms() {
            m_var_atoms.resize(num_vars);
            m_atom_vars.resize(m_atoms.size());
            for (unsigned i = 0; i < m_atoms.size(); ++i) {
                atom * a = m_atoms[i];
                if(a == nullptr) {
                    continue;
                }
                var_vector vec;
                collect_atom_vars(a, vec);
                m_atom_vars[i] = vec;
                for(var v: vec) {
                    m_var_atoms[v].push_back(i);
                }
            }
        }

        void disable_var_atoms(var v) {
            for (unsigned i = 0; i < m_var_atoms[v].size(); ++i) {
                disable_atom(m_var_atoms[v][i]);
            }
        }

        void cache_atom_set(bool_var b, interval_set *s) {
            m_atom_caching_enabled[b] = true;
            m_ism.dec_ref(m_atom_caching_set[b]);
            m_ism.inc_ref(s);
            m_atom_caching_set[b] = s;
        }

        void disable_atom(bool_var b) {
            enlarge_atom(b);
            m_atom_caching_enabled[b] = false;
        }

        bool is_atom_enabled(bool_var b) const {
            // return b >= m_atom_caching_enabled.size() ? false : m_atom_caching_enabled[b];
            return false;
        }

        interval_set * get_atom_set(bool_var b) const {
            return b >= m_atom_caching_set.size() ? nullptr : m_atom_caching_set[b];
        }

        void enlarge_atom(bool_var b) {
            while (m_atom_caching_set.size() <= b) {
                m_atom_caching_set.push_back(nullptr);
                m_atom_caching_enabled.push_back(false);
            }
        }

        ~imp() {}
    };

    nlsat_caching_system::nlsat_caching_system(interval_set_manager &ism, pmanager &pm, atom_vector const &as, clause_vector const &cs) {
        m_imp = new imp(ism, pm, as, cs);
    }

    nlsat_caching_system::~nlsat_caching_system() {
        dealloc(m_imp);
    }

    void nlsat_caching_system::init() {
        m_imp->clear();
    }

    bool nlsat_caching_system::is_atom_enabled(bool_var b) const {
        return m_imp->is_atom_enabled(b);
    }

    void nlsat_caching_system::disable_atom(bool_var b) {
        m_imp->disable_atom(b);
    }

    interval_set * nlsat_caching_system::get_atom_set(bool_var b) const {
        return m_imp->get_atom_set(b);
    }

    void nlsat_caching_system::cache_atom_set(bool_var b, interval_set * s) {
        m_imp->cache_atom_set(b, s);
    }

    void nlsat_caching_system::enlarge_atom(bool_var b) {
        m_imp->enlarge_atom(b);
    }

    void nlsat_caching_system::init_vars(unsigned x) {
        m_imp->init_vars(x);
    }

    void nlsat_caching_system::disable_var_atoms(var v) {
        m_imp->disable_var_atoms(v);
    }
};