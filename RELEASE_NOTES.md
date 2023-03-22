RELEASE NOTES

#benchmark: 6778

Version wzh-ls-v0 (baseline) - 5243
================
- random walk propability: 30%
- greedy case: 
  - insert all arith and bool operations, choose best one with score > 0
  - tie breaking: random choose one
- random walk: 
  1. random select an unsat clause
  2. insert one operation outside the clause infeasible set for each var
  3. insert operation for bool var
  4. random execute bool or arith move

Version wzh-ls-v1 (baseline) - 5098
================
- greedy case first, random walk last, no operation rw finally
