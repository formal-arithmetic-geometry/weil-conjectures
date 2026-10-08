+++
id = "fix-lem-exchanges"
kind = "lemma"
title = "Exchange functoriality: naturality, identities, and pasting"
order = 1647
uses = ["def-cbc-exchange-map", "def-exchange-projection", "def-fix-six-functor-datum", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-pbc-cartesian-square", "def-weil-scheme-morphism-properties", "lem-weil-pbc-exchange-identity-pasting", "prop-compactification-coherence-detailed", "sbc-def-base-change-map", "sbc-lem-identity-and-base-change-composition", "sbc-thm-bounded-below-derived-smooth-base-change", "sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch", "thm-cbc-finite-extension", "thm-cbc-finite-torsion", "thm-cbc-qbar", "thm-sf-comp-composition"]
+++
In the six-functor datum of
[def-fix-six-functor-datum], let

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{g}&Y
\end{array}
$$

be a cartesian square of
finite-type $k$-schemes
whose four arrows are
separated and of finite
type, and let $K\in D^b_c(X,\Lambda)$, with $K'=Lg'^*K$. The
exchange transformations

$$
\operatorname{Ex}_*(K):Lg^*Rf_*K\longrightarrow Rf'_*K',
\qquad
\operatorname{Ex}_!(K):Lg^*Rf_!K\longrightarrow Rf'_!K',
$$

of [def-exchange-projection] satisfy:

1. both are natural in $K$, in the morphisms of the square, and
in the coefficient ring; $\operatorname{Ex}_!$ agrees with the
compact-support exchange map of [def-cbc-exchange-map] at every
finite level and with its transports of
[thm-cbc-finite-extension] and [thm-cbc-qbar] at the
rational and algebraically closed levels;
1. both are the identity for an identity square, and for
vertically or horizontally pasted cartesian squares the exchange
transformation of the outer rectangle is the composite of the
exchange transformations of the two inner squares after inserting
the canonical associativity isomorphisms; $\operatorname{Ex}_*$
obeys the identity and pasting equations of
[lem-weil-pbc-exchange-identity-pasting] and of
[sbc-lem-identity-and-base-change-composition],
$\operatorname{Ex}_!$ those of [thm-cbc-finite-torsion];
1. for smooth $g$,
$\operatorname{Ex}_*$ is the smooth-base-change exchange morphism of
[sbc-thm-bounded-below-derived-smooth-base-change], and it is an
isomorphism;
1. $\operatorname{Ex}_!$ is independent of the chosen
compactification and compatible with the refinement comparison
isomorphisms of [prop-compactification-coherence-detailed] and with the
composition law of [thm-sf-comp-composition].

## Proof

Step 1: construction. By [def-exchange-projection],
$\operatorname{Ex}_*$ is the adjoint of the composite of the
canonical identification $Lf'^*Lg^*\cong Lg'^*Lf^*$ of the
cartesian square ([def-weil-pbc-cartesian-square]) with the
counit of $Lf^*\dashv Rf_*$ of [def-weil-derived-direct-image],
and $\operatorname{Ex}_!$ is represented by $\operatorname{Ex}_*$
for a proper compactification $\bar f$, followed by the
extension-by-zero identification
$L\bar g'^*j_!\cong j'_!Lg'^*$ of [def-exchange-projection]; at
a finite coefficient level the latter is the map of
[def-cbc-exchange-map], whose definition is the same composite.
Step 2: naturality. Each ingredient of these composites is a natural
transformation: the identification of the cartesian square is natural
in the square and the coefficient ring
([def-weil-pbc-cartesian-square]), the counit is natural by
[def-weil-derived-pullback-tensor-hom] and
[def-weil-derived-direct-image], and the extension-by-zero
identification is natural by [def-cbc-exchange-map]; the
transports of [thm-cbc-finite-extension] and
[thm-cbc-qbar] are the coefficient extensions of the same maps.
Step 3: identity and pasting. The identity and pasting equations
for $\operatorname{Ex}_*$ are the mate versions of the identity
and pasting laws of the identification of the cartesian square,
recorded in [lem-weil-pbc-exchange-identity-pasting] (finite
etale coefficients) and in
[sbc-lem-identity-and-base-change-composition] (derived level,
for successive base changes); the identity and horizontal and
vertical pasting for $\operatorname{Ex}_!$ are the corresponding
properties of its two ingredients, stated in
[thm-cbc-finite-torsion], together with
[lem-weil-pbc-exchange-identity-pasting] for the proper factor.
Step 4: smooth base
change. For smooth $g$, $\operatorname{Ex}_*$ is the derived
exchange morphism of [sbc-def-base-change-map] read on the same
square, and it is an isomorphism by
[sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch] at
the algebraically closed rational level and by the corresponding
finite-level statement of [sbc-thm-bounded-below-derived-smooth-base-change]
at the other levels. Step 5: independence. The comparison
isomorphisms of [prop-compactification-coherence-detailed] identify the
two compactification candidates of $\operatorname{Ex}_!$ and are
compatible with the composition law of
[thm-sf-comp-composition] (the proper-composition
isomorphism and the extension-by-zero identification), so
$\operatorname{Ex}_!$ does not depend on the compactification.
