+++
id = "lem-weil-pbc-underived-exchange-sectionwise"
kind = "lemma"
title = "Well-definedness of the sectionwise exchange rule"
order = 1037
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-underived-exchange"]
+++
Let $\square$ be a cartesian square
[def-weil-pbc-cartesian-square], let $F\in\Ab(X_{\Et})$, and let
$V\to Y'$ be etale. For a representative of a section of $g^{-1}f_*F$ over
$V$, consisting of an etale $W\to Y$, a map $V\to W\times_YY'$, and a section
of $F$ on $X\times_YW$, restrict that section along $X'\times_{Y'}V\to
X\times_YW$ and sheafify. The resulting section of $f'_*g'^{-1}F$ over $V$
depends only on the class of that representative in $(g^{-1}f_*F)(V)$, and it
is the section corresponding to the underived exchange morphism
$\Ex^0_{\square,F}$ of [def-weil-pbc-underived-exchange] under the
adjunction $f'^{-1}\dashv f'_*$.

## Proof

By [def-weil-pbc-underived-exchange] the morphism
$\Ex^0_{\square,F}$ is the adjoint, under the adjunction $f'^{-1}\dashv
f'_*$ of [def-weil-pbc-inverse-image], of the composite
$g'^{-1}\varepsilon_f\circ\theta_\square$, where $\theta_\square$ is the
natural isomorphism attached to the chosen identification of the cartesian
square of [def-weil-pbc-cartesian-square] and $\varepsilon_f$ is the
counit of the adjunction $f^{-1}\dashv f_*$. Evaluating that composite on
sections gives the displayed sectionwise rule: the counit
$\varepsilon_f:f^{-1}f_*F\to F$ sends the section of $f^{-1}f_*F$ over $W$
represented by a section of $F$ over $X\times_YW$ to that section, the
isomorphism $\theta_\square$ transports it along the identification $X'\cong
X\times_YY'$ to the section over $X'\times_{Y'}V$, and taking the adjoint of
the composite with respect to $f'^{-1}\dashv f'_*$ is the identity on
sections of the direct image of [def-weil-pbc-direct-image]. Two
representatives of one class in $(g^{-1}f_*F)(V)$, a filtered colimit of
sections over etale $W\to Y$ by [def-weil-pbc-inverse-image], agree over a
common refinement, and the restriction maps of $F$ are compatible with that
refinement, so the resulting section of $f'_*g'^{-1}F$ over $V$ is
independent of the representative.
