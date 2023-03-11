# Version for local search of nra

## Version Description
|name|pick var| random walk|
|-|-|-|
|z3-nra-newest|1/10|1/20|
|z3-nra-v0|always|1/20|
|z3-nra-v1| traditional one|
|z3-nra-v2| random select 5 each step |

## Solving Performance
**benchmark number: 6778**
|name|sat solved|
|-|-|
|z3_origin|5580|
|cvc5_origin|5473|
|z3_nra_newest|5153|
|z3_nra_v0|5131|
|z3_nra_v1|5058|
|z3-nra-v2|5123|