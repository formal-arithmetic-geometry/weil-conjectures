+++
id = "prop-asd-smooth-base-change"
kind = "theorem"
title = "Arbitrary base change for smooth ambient duality"
order = 1577
tags = ["latex:proposition"]
uses = ["cor-amb-affine-space-adjunction", "def-sbc-smooth-morphisms", "def-weil-derived-pullback-tensor-hom", "def-weil-pbc-derived-categories", "lem-amb-cartier-kummer-map", "lem-amb-etale-adjoint-locality", "lem-amb-proper-coproducts-projection", "thm-amb-etale-exceptional-adjoint", "thm-amb-p1-adjunction", "thm-amb-p1-decomposition", "thm-asd-smooth-tensor"]
+++
Let $f:X\to S$ be as in
[thm-asd-smooth-tensor], and let $g:S'\to S$
be any morphism of Noetherian schemes. Denote its base
change by $f':X'\to S'$, with $g':X'\to X$.
The canonical morphism

$$
g'^*f^\times K\longrightarrow f'^\times g^*K
$$

is an isomorphism for every complex $K$. At $K=A$
it identifies $g'^*\omega_f$ with $\omega_{f'}$,
and it respects the tensor isomorphism of
[thm-asd-smooth-tensor].
The notation refers to smooth morphisms, and derived pullback and internal Hom.

## Proof

Proper base change on a compactification, followed by the
stalkwise base-change identity for extension by zero, gives
$Rf'_!g'^*\cong g^*Rf_!$, for bounded-below complexes by the
finite-amplitude argument in
[lem-amb-proper-coproducts-projection]. Define the
displayed map by the adjunction of
[thm-amb-etale-exceptional-adjoint], transposing

$$
Rf'_!g'^*f^\times K\cong g^*Rf_!f^\times K
\longrightarrow g^*K.
$$

For a projective-line projection its unit and counit are
those explicitly constructed in
[thm-amb-p1-adjunction]. Both commute with base change:
the supported diagonal class does so by
[lem-amb-cartier-kummer-map], and the trace does so
by [thm-amb-p1-decomposition]. Hence the displayed
map in that case is the ordinary inverse-image and twist
base-change isomorphism. The same holds for an affine-line
projection by restricting its projective compactification,
and for affine space by composing those adjunctions.

It remains to verify the three coherences on which the identification
rests; each is a statement about the canonical maps, not merely about
their sources and targets.
*(i) The underlying base-change map in the model case.*
For the affine-space projection $\mathbf A^d_{S_0}\to S_0$
over a Zariski open $S_0\subseteq S$, the identification
$Rf'_!g'^*\cong g^*Rf_!$ of the first paragraph is the composite of
proper base change for the compactification
$\mathbf A^d\hookrightarrow\mathbf P^d$ with the stalkwise identity
$g^*j_!=j'_!g'^*$ for the extension by zero; both are comparisons of
the two diagrams obtained by base changing one diagram along $g$,
so the composite restricts to the chart $S'_0=S'\times_SS_0$.
*(ii) Unit and counit on the chart.* There the adjunction of
[thm-amb-etale-exceptional-adjoint] is the affine-space adjunction
[cor-amb-affine-space-adjunction], whose unit and counit are built
from the trace and the supported diagonal class; these commute with
base change by [lem-amb-cartier-kummer-map] and
[thm-amb-p1-decomposition]. The displayed map is the transpose of
the counit composite, so the base-change isomorphism of (i) carries it
to the corresponding transpose over $S'_0$, which is the map defined
by the same recipe there.
*(iii) Descent to $X'$.* On the etale chart of $f$ used in
the proof of [thm-asd-smooth-tensor],
[lem-amb-etale-adjoint-locality] identifies the map under
consideration with the base-change isomorphism of (ii) preceded by
etale inverse image, the sum over the finite fibre commuting with base
change; it is therefore an isomorphism on an etale cover of $X'$,
hence everywhere. Finally the tensor maps of
[thm-asd-smooth-tensor] were transposed from the projection
formula and the counit, and applying the same transposition to the
commuting base-change diagram of those two maps gives their base-change
compatibility. This proves all the claimed identifications.
