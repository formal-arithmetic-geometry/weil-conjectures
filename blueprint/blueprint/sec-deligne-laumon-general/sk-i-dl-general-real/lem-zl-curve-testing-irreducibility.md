+++
id = "lem-zl-curve-testing-irreducibility"
kind = "lemma"
title = "Curve testing for geometric irreducibility"
order = 2832
uses = ["def-weil-pbc-qbar-category", "def-wf-fundamental-representation", "lem-zl-bertini-finite-cover-curve", "lem-zl-finite-matrix-irreducibility"]
+++
Let $X_0$ be a smooth geometrically connected affine scheme over a
finite field, and let $\mathcal S_1,\ldots,\mathcal S_r$ be lisse
$\Qlb$-Weil sheaves whose geometric restrictions are irreducible.
Given a nonempty finite set of geometric points of $X_0$ over
closed points, if $\dim X_0\geq1$, there is, after a finite
constant-field extension, a smooth geometrically connected affine
curve in $X_0$ through these points on which every
$\mathcal S_j$ remains geometrically irreducible.

## Proof

Use the geometric representations of
[def-wf-fundamental-representation], and choose finite coefficient
fields for them as allowed in [def-weil-pbc-qbar-category].
By [lem-zl-finite-matrix-irreducibility], each has a finite
reduction quotient detecting absolute irreducibility. Intersect
their open normal kernels in $\pi_1(X)$, where
$X=X_0\times\overline{\mathbf F}_q$. The resulting finite quotient
$Q$ corresponds to a connected finite etale Galois cover $T\to X$.
For $\dim X\geq2$, apply
[lem-zl-bertini-finite-cover-curve]. Connectedness of the
restricted $Q$-torsor means that the image of $\pi_1(C)$ acts
transitively on $Q$, hence is all of $Q$. It surjects onto each
chosen reduction quotient. The finite matrix witnesses show that
all the restricted geometric representations remain irreducible.
The curve and inclusion descend to a finite constant extension;
the restrictions inherit their Weil structures over that field.
For dimension one take $C=X$, with its given finite-field model.
