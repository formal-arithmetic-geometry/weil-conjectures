+++
id = "lemma-weil-pbc-proper-underived-exchange"
kind = "lemma"
title = "Underived proper exchange is an isomorphism"
order = 1091
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "def-weil-pbc-underived-exchange", "lemma-weil-pbc-geometric-stalk-conservative", "lemma-weil-pbc-proper-strict-henselian-h0", "lemma-weil-pbc-underived-exchange-naturality", "prop-weil-pbc-strict-henselization-stalk-formula"]
+++
If $f$ is proper, then
$\operatorname{Ex}_{\square,F}:g^{-1}f_*F\to f'_*g'^{-1}F$ is an
isomorphism for every sheaf $F$.

## Proof

Fix a geometric point $\bar y'\to Y'$ and let $\bar y\to Y$ be its composite
with $g$. Let $\mathcal N_{\bar y}^{\mathrm{aff}}$ be the category of
pointed affine etale neighbourhoods $(V,\bar v)$ of $\bar y$. It is
cofiltered: an affine open containing the lifted point in a fibre product
refines two objects, and an affine neighbourhood of the equalizer of two
maps makes parallel maps equal. It is cofinal among all pointed etale
neighbourhoods because every lifted point has an affine open neighbourhood.
Thus

$$
(f_*F)_{\bar y}=
\varinjlim_{(V,\bar v)}\Gamma(X\times_YV,F|).
$$

Writing $V=\operatorname{Spec}A_V$, the strict henselization is
$Y_{(\bar y)}=\operatorname{Spec}(\varinjlim A_V)$ and
$X_{(\bar y)}=X\times_YY_{(\bar y)}=\varprojlim(X\times_YV)$. The natural
map from the displayed colimit to $\Gamma(X_{(\bar y)},F|)$ is bijective.
For surjectivity, represent a section on the limit by sections on a finite
cover by quasi-compact etale objects. Each object, each covering map, and
each section representative descends to a stage because etale morphisms are
locally of finite presentation. The finitely many equality conditions on
the pairwise fibre products descend after enlarging that stage. The sheaf
equalizer then glues the descended representatives. For injectivity,
represent two sections at one stage; equality on the limit is witnessed on
a finite etale cover, and the cover together with its finitely many equality
witnesses descends to a later stage. Hence the two representatives agree in
the colimit.

The base $Y_{(\bar y)}$ is strictly henselian local and
$X_{(\bar y)}$ is proper over it. The preceding lemma identifies its
sections with those on the closed geometric fibre:

$$
(f_*F)_{\bar y}\xrightarrow{\sim}
\Gamma(X_{(\bar y)},F|)\xrightarrow{\sim}
\Gamma(X_{\bar y},F|_{X_{\bar y}}).
$$

The identical construction for $f'$ gives the target stalk. Since $\bar y$
is the composite of the same $\operatorname{Spec}\Omega\to Y'$ with $g$,
the Cartesian isomorphism identifies $X_{\bar y}$ and $X'_{\bar y'}$ with
$X\times_Y\operatorname{Spec}\Omega$.

Finally, a germ represented by $s\in\Gamma(X\times_YV,F|)$ travels around
the comparison by pulling $s$ first to $X'\times_{Y'}(V\times_YY')$ and then
to the geometric fibre. The two stalk identifications above pull $s$
directly to that same fibre. Hence the fibre bijection is the stalk of
$\operatorname{Ex}_{\square,F}$, not an unnamed isomorphism. Geometric
stalks are conservative, so the exchange map is an isomorphism. This closes
the compatibility omission at Tag `0A3U`.

## Detailed form

For a cartesian square [def-weil-pbc-cartesian-square] with $f$
proper [def-weil-pbc-scheme-conventions] and every torsion etale sheaf
[def-weil-pbc-etale-sheaves] $F$ on $X_{\Et}$, the map

$$
 \Ex^0_{\square,F}:g^{-1}f_*F\xrightarrow{\sim}f'_*g'^{-1}F
$$

of [def-weil-pbc-underived-exchange] is an isomorphism.

## Proof

Fix a geometric point $\bar y'=\operatorname{Spec}\Omega\to Y'$ and let $\bar
y$ be its composite with $Y'\to Y$. By
[prop-weil-pbc-strict-henselization-stalk-formula], the stalks of
both sides at $\bar y'$ are computed by sections on the fibres over the
strict henselizations of the two residue fields, and
[lemma-weil-pbc-proper-strict-henselian-h0] identifies those sections with
sections on the corresponding closed geometric fibres. The chosen
identification of [def-weil-pbc-cartesian-square] identifies these
two fibres and the two coefficient sheaves, and expanding the
unit--$\theta_\square$--counit composite of
[def-weil-pbc-underived-exchange] shows that the induced stalk map
is the identity under these identifications. Geometric stalks are
conservative by [lemma-weil-pbc-geometric-stalk-conservative], so the map is an
isomorphism.
