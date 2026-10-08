+++
id = "sk-prop-av-connected-order"
kind = "section"
title = "Connected finite group schemes have $p$-power order"
lean = ["AlgebraicGeometry.exists_finrankΓ_eq_pow"]
order = 575
uses = ["sk-def-av-group-scheme"]
+++
*Proposition (sketch).*

Let $G$ be a finite flat group scheme over a field $k$ of
characteristic $p>0$. If $G$ is connected, then $\lvert G\rvert$ is a
power of $p$.

## Proof

Write $G=\Spec A$ with $A$ a finite local Hopf $k$-algebra and
$\mathfrak m=\ker(A\to k)$ nilpotent. The graded algebra
$\mathrm{gr}A$ is a connected graded commutative Hopf algebra; its
primitive elements generate it (subtract comultiplication corrections
from a homogeneous element of least degree). They form a restricted
Lie algebra $\mathfrak g$ with $p$-operation $x\mapsto x^{[p]}$
induced by $x\mapsto x^p$, and $\mathrm{gr}A\cong u(\mathfrak g)$ by
the Milnor–Moore structure theorem. By the restricted PBW theorem
the ordered monomials $x_1^{a_1}\cdots x_r^{a_r}$, $0\le a_i<p$, form a
$k$-basis of $u(\mathfrak g)$; hence
$\lvert G\rvert=\dim_kA=\dim_ku(\mathfrak g)=p^r$.

Uses: [sk-def-av-group-scheme]
