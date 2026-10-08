+++
id = "thm-pur-affine-line-orientation"
kind = "theorem"
title = "Global orientation and its normalization"
order = 1947
uses = ["def-pur-affine-line-datum", "def-pur-conventions", "def-weil-exceptional-inverse-image", "lem-amb-cartier-kummer-map", "lem-exc-closed-ambient", "lem-exc-closed-amplitude", "lem-exc-open-complement-known", "lem-pur-gysin-structure", "lem-pur-support-localization-triangle", "prop-exc-closed-tor", "prop-pur-gm-relative-kummer", "thm-pur-rank-one-local-calculation", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), let $Y$ be the separated finite-type $k$-scheme of the
affine-line datum, and let
$\kappa(t)\in H^1(\mathbf G_{m,Y},A(1))$ be the
Kummer class of the global coordinate
$t$. The boundary of $\kappa(t)$, determined through the
identification of [lem-pur-gysin-structure] (which gives the
support object $Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]\in D^b_{ctf}(Y,\Lambda)$
concentrated in degree zero), is the *global orientation* – a
morphism

$$
\operatorname{pur}_s:\Lambda_Y\longrightarrow Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]
$$

in $D^b_{ctf}(Y,\Lambda)$ with $\Lambda=A$, where $Rs^!$ is the
exceptional inverse image
of the zero section $s:Y\hookrightarrow\mathbf A^1_Y$, a closed
immersion whose ambient right adjoint exists unconditionally
([lem-exc-closed-ambient]) and preserves constructibility and
finite Tor amplitude, the open complement
$\mathbf G_{m,Y}\hookrightarrow\mathbf A^1_Y$ satisfying the
open-complement condition of
[lem-exc-closed-amplitude], [prop-exc-closed-tor] by
[lem-exc-open-complement-known],
with the shift $[2]$ and the twist
$(1)$. Its restriction to every geometric point $\bar y\to Y$ is
the normalized class $1\in H^2_{s(\bar y)}(\mathbf A^1_{\bar y},\Lambda(1))$ of
[thm-pur-rank-one-local-calculation]. (Source: the affine-line
case of cohomological purity, obtained from the Kummer sequence and the
fundamental class of the zero section; Milne, Lectures on Etale
Cohomology, Section 16, Theorems 16.1 and 16.7, and Proposition 16.11
(the case $r=2c-1=1$ of the Gysin sequence of the divisor), with the
acyclicity of the affine line computed in Example 16.3, for the
relative form over a base scheme $Y$.)

## Proof

The Kummer boundary defines the global morphism in the statement by
[lem-pur-gysin-structure], [def-pur-affine-line-datum].
Its target is already a sheaf in degree zero, identified there with
$\Lambda_Y$ through the boundary $\delta$ of the localization triangle
of [lem-pur-support-localization-triangle] pushed forward to $Y$:
$\delta$ carries $R^1\pi_*\Lambda(1)$, free of rank one on $\kappa(t)$
by [prop-pur-gm-relative-kummer](2), isomorphically onto
$\mathcal H^2(Rs^!\Lambda(1))$. So $\operatorname{pur}_s$, which sends
$1$ to the boundary of $\kappa(t)$, already maps $1$ to a generator of
this free rank-one sheaf.
The supported Cartier map of [lem-amb-cartier-kummer-map] is natural
for the base changes of the zero section, and its geometric fibre is
the coordinate boundary. By [thm-pur-rank-one-local-calculation]
that boundary is $1$. Consequently the morphism of degree-zero
sheaves has every stalk equal to the identity, and is an isomorphism.
The etale-origin comparison of [thm-weil-pbc-site-comparison]
transports the assertion and its normalization to the stated site.
Uniqueness follows because a section of a sheaf is determined by its
stalks; this does not require a conservativity assertion for morphisms
of arbitrary derived objects.
