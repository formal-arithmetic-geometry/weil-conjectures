+++
id = "sk-d-lines"
kind = "section"
title = "The affine and projective lines"
order = 2374
uses = ["sk-d-setup"]
lean = ["AlgebraicGeometry.ProjectiveSpace"]
+++
*Remark (sketch).*

Over a finite field $F$ from the coefficient setup,
put $\mathbf A^1_F=\operatorname{Spec}F[t]$.
Glue $\operatorname{Spec}F[t]$ to $\operatorname{Spec}F[z]$ along
$F[t,t^{-1}]=F[z,z^{-1}]$, with $z=t^{-1}$, to obtain $\mathbf P^1_F$.
The first chart is $\mathbf A^1_F$ and its complement is the point
$\infty$ defined by $z=0$. Frobenius acts by $t\mapsto t^{|F|}$ and
$z\mapsto z^{|F|}$ on these charts.

Uses: [sk-d-setup]
