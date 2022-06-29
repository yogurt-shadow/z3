/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    totalizer.cpp

Abstract:
   
    Incremental totalizer for at least constraints

Author:

    Nikolaj Bjorner (nbjorner) 2022-06-27

--*/

#include "opt/totalizer.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include <iostream>

namespace opt {
    
    
    void totalizer::ensure_bound(node* n, unsigned k) {
        auto& lits = n->m_literals;
        if (k > lits.size())
            return;
        auto* l = n->m_left;
        auto* r = n->m_right;
        if (l)
            ensure_bound(l, k);
        if (r)
            ensure_bound(r, k);

        for (unsigned i = k; i > 0 && !lits.get(i - 1); --i) {
            if (l->m_literals.size() + r->m_literals.size() < i) {
                lits[i - 1] = m.mk_false();
                continue;
            }

            expr* c = m.mk_fresh_const("c", m.mk_bool_sort());
            lits[i - 1] = c;

            // >= 3
            // r[2] => >= 3
            // l[0] & r[1] => >= 3
            // l[1] & r[0] => >= 3
            // l[2] => >= 3

            for (unsigned j1 = 0; j1 <= i; ++j1) {
                unsigned j2 = i - j1;
                if (j1 > l->m_literals.size())
                    continue;
                if (j2 > r->m_literals.size())
                    continue;
                expr_ref_vector clause(m);
                if (0 < j1) {
                    expr* a = l->m_literals.get(j1 - 1);
                    clause.push_back(mk_not(m, a));
                }
                if (0 < j2) {
                    expr* b = r->m_literals.get(j2 - 1);
                    clause.push_back(mk_not(m, b));
                }
                if (clause.empty())
                    continue;
                clause.push_back(c);
                m_clauses.push_back(clause);
            }
        }
    }

    totalizer::totalizer(expr_ref_vector const& literals):
        m(literals.m()),
        m_literals(literals),
        m_tree(nullptr) {
        ptr_vector<node> trees;
        for (expr* e : literals) {
            expr_ref_vector ls(m);
            ls.push_back(e);
            trees.push_back(alloc(node, ls));            
        }
        for (unsigned i = 0; i + 1 < trees.size(); i += 2) {
            node* left = trees[i];
            node* right = trees[i + 1];
            expr_ref_vector ls(m);
            ls.resize(left->m_literals.size() + right->m_literals.size());
            node* n = alloc(node, ls);
            n->m_left = left;
            n->m_right = right;
            trees.push_back(n);
        }
        m_tree = trees.back();
    }
        
    totalizer::~totalizer() {
        ptr_vector<node> trees;
        trees.push_back(m_tree);
        while (!trees.empty()) {
            node* n = trees.back();
            trees.pop_back();
            if (n->m_left)
                trees.push_back(n->m_left);
            if (n->m_right)
                trees.push_back(n->m_right);
            dealloc(n);
        }
    }
    
    expr* totalizer::at_least(unsigned k) {
        if (k == 0)
            return m.mk_true();
        if  (m_tree->m_literals.size() < k)
            return m.mk_false();
        SASSERT(1 <= k && k <= m_tree->m_literals.size());
        ensure_bound(m_tree, k);
        return m_tree->m_literals.get(k - 1);
    }
    
}
