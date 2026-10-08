+++
id = "lem-weil-pbc-normal-constant-generic"
kind = "lemma"
title = "Constant sheaves on a normal scheme and the generic point"
order = 1129
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselization-limit", "lemma-weil-pbc-etale-cohomology-continuity", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $Y$ be an integral normal scheme with function field $K$, let
$g:\operatorname{Spec}K\to Y$ be the inclusion of the generic point, and let
$\underline E$ be the constant etale sheaf with value a finite abelian group
$E$. Then the canonical map $\underline E\to g_*\underline E$ is an
isomorphism. The same holds for the inclusion $j:U\hookrightarrow Y$ of a
nonempty open subscheme.
(*Stacks Project, Etale Cohomology, Lemma 59.73.13, Tag
[09Z5](https://stacks.math.columbia.edu/tag/09Z5).*)

## Proof

Let $\bar y\to Y$ be a geometric point and let $Y_{(\bar
y)}=\operatorname{Spec}\mathcal O^{sh}_{Y,\bar y}$ be the strict
henselization limit [def-weil-pbc-strict-henselization-limit]. By
[def-weil-pbc-geometric-stalks] the stalk $(g_*\underline E)_{\bar y}$ is the
filtered colimit of $\underline E(\operatorname{Spec}K\times_YV)$ over the
pointed etale neighbourhoods $V$ of $\bar y$, and
[lemma-weil-pbc-etale-cohomology-continuity] in degree zero identifies this
colimit with

$$
 (g_*\underline E)_{\bar y}
 =\underline E\bigl(\operatorname{Spec}K\times_YY_{(\bar y)}\bigr).
$$

Now $\mathcal O^{sh}_{Y,\bar y}$ is a normal domain: it is a strict
henselization of the local ring of the normal scheme $Y$ at $y$, and the
strict henselization of a normal local ring is normal (Stacks Project, More on
Algebra, Lemma 15.46.6, Tag
[06DI](https://stacks.math.columbia.edu/tag/06DI)). Its fraction field is a
finite extension of $K$, so $K\otimes_{\mathcal O_{Y,y}}\mathcal
O^{sh}_{Y,\bar y}$, the localization of that domain at the nonzero elements of
$\mathcal O_{Y,y}$, is a domain as well. Hence $\operatorname{Spec}K\times_YY_{(\bar
y)}$ is irreducible, and a locally constant function on an irreducible scheme
with values in a discrete set is constant, by the description of the constant
sheaf in [def-weil-pbc-etale-sheaves]; therefore $\underline
E(\operatorname{Spec}K\times_YY_{(\bar y)})=E=\underline E_{\bar y}$ and the
canonical map is an isomorphism on the stalk at $\bar y$. This holds at every
geometric point, so the map is an isomorphism by
[lemma-weil-pbc-geometric-stalk-conservative]. For a nonempty open
$j:U\hookrightarrow Y$ the same computation applies, the fibre product
$U\times_YY_{(\bar y)}$ being nonempty and irreducible over each affine open of
$Y$ because $U$ contains the generic point.
