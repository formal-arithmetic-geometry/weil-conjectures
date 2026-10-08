+++
id = "lemma-nagata-power-torsion-submodule"
kind = "lemma"
title = "Power torsion is a submodule"
order = 139
lean = ["Submodule.powTorsion"]
uses = ["def-nagata-power-torsion"]
+++
The subset $\Gamma_{(a)}(M)$ contains zero and is closed under addition and
scalar multiplication.

## Proof

Zero is killed by $a^0$. If $a^mm_1=0$ and $a^nm_2=0$, then
$a^{m+n}(m_1+m_2)=0$. If $r\in R$, then
$a^m(rm_1)=r(a^mm_1)=0$.
