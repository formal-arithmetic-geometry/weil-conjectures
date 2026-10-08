+++
id = "lem-kun-0f1c"
kind = "lemma"
title = "Direct image commutes with base change along field extensions"
order = 1758
uses = ["def-kun-separably-closed", "def-weil-pbc-scheme-conventions", "lem-kun-0f09", "lem-kun-separable-smooth-colimit", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $L/K$ be an extension of fields and $g:T\to S$ a
quasi-compact and
quasi-separated morphism of schemes over $K$; denote
$g_L:T_L\to S_L$ the base change to $\Spec(L)$. Let
$E\in\Dplus(T_{\Et})$ have cohomology sheaves whose stalks are
torsion of orders invertible in $K$, and let $E_L$ be the pullback
of $E$ to $(T_L)_{\Et}$. Then $Rg_{L,*}E_L$ is the pullback of
$Rg_*E$ to $S_L$.
(*Source:* Stacks Project,
[Tag `0F1C`](https://stacks.math.columbia.edu/tag/0F1C); the proof
below follows the reduction recorded there.)

## Proof

*Step 1 (reduction to perfect fields).* Let $K'\supseteq K$ and
$L'\supseteq L$ be the perfect closures. The extensions $K'/K$ and
$L'/L$ are purely inseparable, so $\Spec(K')\to\Spec(K)$ and
$\Spec(L')\to\Spec(L)$ are universal homeomorphisms in the sense of
[def-weil-pbc-scheme-conventions]; by the invariance of the small etale
topos under universal homeomorphisms
([thm-weil-pbc-universal-homeomorphism-invariance]) the inverse and
direct images of the two squares are identified under these base changes, so
the assertion for $L/K$ is equivalent to the assertion for $L'/K'$. As
$K'$ is perfect, the extension $L'/K'$ is separable
([def-kun-separably-closed]).

*Step 2 (separable extensions).* By
[lem-kun-separable-smooth-colimit] the field $L'$ is a filtered
colimit of finitely generated smooth $K'$-subalgebras with the inclusions as
transition maps, so $\Spec(L')$ is the inverse limit of the affine smooth
$K'$-schemes $\Spec(A_i)$ with affine transition morphisms; these are
quasi-compact and quasi-separated. Apply the limit form of smooth base change
[lem-kun-0f09] with $S=\Spec(K')$, $S'=\Spec(L')$, the quasi-compact
quasi-separated morphism $g_{K'}:T_{K'}\to S_{K'}$ and the coefficient
complex $E_{K'}\in\Dplus$ whose cohomology sheaves have torsion stalks of
orders invertible in $K'$: it gives

$$
g_{L'}^{-1}Rg_{K',*}E_{K'}\xrightarrow{\ \sim\ }Rg_{L',*}(g')^{-1}E_{K'},
$$

which is the assertion for the separable extension $L'/K'$, and hence, by
Step 1, the assertion for $L/K$.
