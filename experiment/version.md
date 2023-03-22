# Version for local search of nra

## Version Description -wzh-ls
|name|pick var| random walk|
|-|-|-|
|z3_nra_newest|1/10|1/20|
|z3_nra_v0|always|1/20|
|z3_nra_v1| traditional one|
|z3_nra_v2| random select 5 each step |
|z3_nra_v3| insert one unsat literal for each unsat clause |
|z3_nra_v4| format traditional one |

## Solving Performance -wzh-ls
**benchmark number: 6778**
|name|sat solved|
|-|-|
|z3_origin|5580|
|cvc5_origin|5473|
|z3_nra_newest|5153|
|z3_nra_v0|5131|
|z3_nra_v1|5058|
|z3_nra_v2|5123|
|z3_nra_v3|5072|
|z3_nra_v4|4945|

## Version Compare -z3-nra-ls
|z3_branch_v0|d276ac1 (baseline)|
|z3_branch_v1|greedy first, random next, no operation last|

## Solving Performance -wzh-ls
**benchmark number: 6778**
|name|sat solved|
|-|-|
|z3_branch_v0|5243|
