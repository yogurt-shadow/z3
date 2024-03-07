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
## 第一版算法
### Search:
![](https://cdn.nlark.com/yuque/0/2024/jpeg/26979990/1709718473151-d10851cd-1d5a-4922-b4a2-114e2bc83a1c.jpeg)
### Conflict Analysis
这里主要有四种分类

- 布尔冲突
   - 之前有decide
   - 之前没有decide
- 算术冲突
   - 存在semantic decision
   - 不存在semantic decision （完全由arithmetic value造成）

此时应该对应四种算法，假定我们目前和z3一样，尝试回退到decision level，然后选择其他路径（虽然这在cls-lvl的做法中是不被提倡的）

1. 布尔冲突
   1. 之前有decide: 回退到decision level，然后尝试process clause
   2. 之前没有decide?
2. 算术冲突
   1. 存在semantic decision，此时的lemma应该含有一个decision literal，回退到decision level，然后process lemma，为了得到decision literal否定的赋值
   2. 不存在semantic decision，回退到stage，然后根据新的lemma从新计算clause-infeasible，继续path case和full case的分支
