+++
id = "lem-zl-affine-curve-hc2-purity"
kind = "lemma"
title = "Purity of the top affine-curve factor"
order = 2840
uses = ["def-weil-frobenius-module-weights", "def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "lem-a1-affine-hc2-pure"]
+++
Let $C_0$ be a smooth affine curve and let $\mathcal E$ be lisse and
punctually $\iota$-pure of weight zero. Every nonzero Frobenius
eigenvalue on $H_c^2(C,\mathcal E)$ has weight two.

## Proof

First assume that $C_0$ is geometrically connected. Then
[lem-a1-affine-hc2-pure], applied with $w=0$, shows that
$H_c^2(C,\mathcal E)$ is $\iota$-pure of weight two in
[def-weil-frobenius-module-weights]: every Frobenius eigenvalue on it
has $\iota$-modulus $q$.

For a general smooth affine curve, choose a finite extension
$\mathbf F_{q^e}/\mathbf F_q$ over which all its finitely many
geometric connected components are defined. This is possible because
each open and closed component is specified by an idempotent in its
affine coordinate ring after base change to $\overline{\mathbf F}_q$,
and the finitely many coefficients of these idempotents lie in a
finite extension. Over $\mathbf F_{q^e}$ the curve is a finite
disjoint union of geometrically connected smooth affine curves.
The restricted sheaves remain punctually pure of weight zero:
if a closed point $z$ of the base change maps to $x\in C_0$,
the Frobenius on its stalk is $F_x^{[\kappa(z):\kappa(x)]}$.
Every eigenvalue is therefore a positive integral power of an
eigenvalue of $F_x$, and still has modulus one, as required by
[def-weil-punctual-weights]. Apply the preceding argument to
each component and take the direct sum of their compactly supported
cohomology. Every eigenvalue of $F^e$ on this sum has modulus
$q^e$. If $\lambda$ is an eigenvalue of $F$, then
$\lambda^e$ is an eigenvalue of $F^e$, so
$\lvert\iota(\lambda)\rvert^e=q^e$, and
$\lvert\iota(\lambda)\rvert=q$. The empty curve has zero
cohomology, so its assertion is vacuous.
