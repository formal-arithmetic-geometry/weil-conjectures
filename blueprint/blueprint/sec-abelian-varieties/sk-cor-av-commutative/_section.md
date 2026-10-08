+++
id = "sk-cor-av-commutative"
kind = "section"
title = "Abelian varieties are commutative"
lean = ["AlgebraicGeometry.IsAbelianScheme.isCommMonObj", "AlgebraicGeometry.IsAbelianScheme.isCommMonObj_of_field"]
order = 491
uses = ["sk-def-av", "sk-prop-av-rigidity"]
+++
*Corollary (sketch).*

Let $A$ be an abelian variety over $k$. Then $m\circ s=m$, i.e. $A$
is commutative and $A(k)$ is an abelian group.

## Proof

The commutator map $c:A\times_kA\to A$, $(x,y)\mapsto xyx^{-1}y^{-1}$,
satisfies $c(A\times\{e\})=\{e\}$; applying [sk-prop-av-rigidity] with
$X=Y=Z=A$ and $y_0=e$ gives $c(x,y)=c(e,y)=e$ for all $x,y$. (The
hypotheses hold: $A$ is proper and separated of finite type, geometrically
reduced since smooth, and geometrically connected since it is connected
with the rational point $e$, `04KV`.)

Uses: [sk-def-av], [sk-prop-av-rigidity]
