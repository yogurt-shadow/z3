# Version for Hybrid Dynamic Nlsat

## Version Description
| name |branching heuristic| restart | learned management | unit propagate | date |
|-|-|-|-|-|-|
|uniform_mcsat_origin|uniform_vsids | off|off|off| 23/02/27 |
|uniform_mcsat_restart| uniform_vsids|on|off|off|23/02/28|

## Solving Performance
**benchmark number: 12134**
|name| solved| sat| unsat | unsolved |
|-|-|-|-|-|
|uniform_mcsat_origin| 10883| 5611|5272|1251|
|uniform_mcsat_restart| 10967|5612|5355|1167|
|z3_mcsat| 10730|5546|5184|1404|
|z3_origin|10936|5580|5356|1198|
