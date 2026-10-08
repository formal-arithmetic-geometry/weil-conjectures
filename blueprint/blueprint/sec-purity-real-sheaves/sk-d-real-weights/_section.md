+++
id = "sk-d-real-weights"
kind = "section"
title = "Local weights and reality"
order = 2588
uses = ["sk-d-real-setup", "sk-d-real-weil"]
lean = ["AlgebraicGeometry.WeilGroup.IsPunctuallyPure", "AlgebraicGeometry.WeilGroup.frobeniusWeight", "AlgebraicGeometry.WeilGroup.localPolynomial", "AlgebraicGeometry.WeilGroup.HasWeightsAtMost", "AlgebraicGeometry.WeilGroup.IsReal"]
+++
*Definition (sketch).*

For a Weil sheaf $\mathcal F$, use the
determinant to set

$$
P_x(\mathcal F,T)=\det(1-TF_x\mid\mathcal F_{\bar x}),\qquad
\wt_{\iota,q_x}(\alpha)=
\frac{2\log|\iota(\alpha)|}{\log q_x}
$$

for a nonzero local eigenvalue $\alpha$ and the
residue cardinality $q_x$.
The sheaf is punctually $\iota$-pure of weight $w$ if all these weights
are $w$, and has weights at most $w$ if all are $\le w$.
It is $\iota$-real if $\iota P_x(\mathcal F,T)\in\mathbf R[T]$ for every
$x$, equivalently if each complex local eigenvalue multiset is stable
under complex conjugation. This condition is imposed on polynomials.

Uses: [sk-d-real-setup], [sk-d-real-weil]
