+++
id = "lem-fix-weil-operations"
kind = "lemma"
title = "Weil structures on operations and their basic maps"
order = 2108
uses = ["def-coefficient-twists-detailed", "def-compact-support-direct-image-detailed", "def-exchange-projection", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-frobenius-detailed", "def-weil-weil-sheaf-complex", "fix-lem-exchanges", "fix-prop-adjunctions"]
+++
Let $f_0:X_0\to Y_0$ be a separated finite-type morphism over the
finite base field, and let $f:X\to Y$ be its geometric fiber.
Use $\Lambda=E$ or $\Qlb$ and the
Weil-complex categories.
On any of the stated domains on which the underlying operations
preserve bounded constructibility, pullback, the two direct images,
tensor and internal Hom carry canonical Weil structures. An
admissible
exceptional adjoint carries one as well. Tensor evaluation, the
adjunction units and counits, composition comparisons, exchange maps,
and the projection transformation are equivariant. The
coefficient twists carry their
prescribed Frobenius actions. These assertions concern the underlying
operations and their algebraic maps; equivariance of a geometric
smooth-purity orientation requires its separate theorem.
(For finite coefficients, a scheme-Frobenius form of the $Rf_!$
comparison, which also applies to non-invertible Frobenius coefficient
morphisms, is constructed later in [def-trf-weil-shriek-pushforward];
it is not used here.)

## Proof

Write $g_X,g_Y$ for the geometric-Frobenius automorphisms of
[def-weil-frobenius-detailed]. For $Rf_*$, define its Weil isomorphism
by

$$
g_Y^*Rf_*K\xrightarrow{\operatorname{Ex}_*}
Rf_*g_X^*K\xrightarrow{Rf_*\theta_K}Rf_*K.
$$

The exchange of [fix-lem-exchanges] is an isomorphism for an
automorphism square: the inverse comes from the inverse square and
their pasting is the identity. The pasting identity proves the
iterate compatibility required by
[def-weil-weil-sheaf-complex]. The same construction with
$\operatorname{Ex}_!$ defines the Weil structure on
[def-compact-support-direct-image-detailed]. Pullback uses
$g_X^*f^*=f^*g_Y^*$. Tensor and internal Hom use the natural
identifications of [def-weil-derived-pullback-tensor-hom]; for
internal Hom the inverse Weil map on its contravariant argument is
used. Since $g^*$ is an equivalence, this Hom identification does
not require a claim that every constructible complex is site-perfect.

For an admissible exceptional adjoint, take the mate of the
$Rf_!$ comparison under [fix-prop-adjunctions]. Inverse
automorphism squares again give its inverse, and mate calculus proves
that its units and counits are equivariant, using the adjoint of
[def-weil-exceptional-adjoint-admissibility].
For the ordinary adjunction of [def-weil-derived-direct-image]
the same assertion is the definition of $\operatorname{Ex}_*$.
Evaluation is natural in the two Weil maps and their inverses, so
its square commutes. Composition and exchange use the pasting
identities of [fix-lem-exchanges]; the projection transformation
of [def-exchange-projection] is a composite of precisely these
tensor and counit maps, hence is equivariant as well.
Finally [def-coefficient-twists-detailed] fixes the scalar Frobenius
action on each twist, and tensoring with that scalar respects all
the maps above.
