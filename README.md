# Clause-Level MCSAT
## 目前焦点
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709640289984-3ff1fc0b-e3d5-49b7-bcc4-3c3d88924eaf.jpeg)

在选择到path case之后，仍然需要decide literal，但是这个时候的decide是伪decide （任何一种选择不会产生path）。
z3原生产生子句后，会回退到decide层面的trail，然后尝试选择其他literal,这一点在cls-lvl可以避免。
问题是cls-lvl要回退到哪一层？
## Set Path for Arithmetic Variable
One-Level Path:
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709705681160-97a5da0a-8928-4fc0-a9f9-cdb31343de04.jpeg)
Two-Level Path:
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709706890966-efe234ff-7a09-49cd-b749-e4797d3f9e1a.jpeg)
## shortcut for unsat (只有一个变量)
当前process的clauses只还有一个变量(max var)，并且组成的satisfying interval为空集，直接返回unsat
## common case (仍然含有多个变量，此时应该怎么学习子句？)
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709711558096-a333b6ea-42ac-4a68-906d-4f05e825b95a.jpeg)
目前做法：
在found decision之后，回退到block状态，然后继续尝试其他选择，以生成完整的多path下的lemma
undo_until_block()
## 尝试改进full case下的path方法
