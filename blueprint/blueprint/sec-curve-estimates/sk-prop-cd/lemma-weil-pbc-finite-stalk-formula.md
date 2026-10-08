+++
id = "lemma-weil-pbc-finite-stalk-formula"
kind = "lemma"
title = "Geometric stalk formula for finite direct image"
order = 997
lean = ["AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi", "AlgebraicGeometry.Etale.stalkRestrict"]
uses = ["def-kun-separably-closed", "def-weil-pbc-cartesian-square", "def-weil-pbc-direct-image", "def-weil-pbc-geometric-fibre", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions", "lem-fin-finite-splitting", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $h:W\to V$ be finite and let $\bar v:\operatorname{Spec}\Omega\to V$ be a geometric
point with $\Omega$ algebraically closed. For every sheaf $F$ on $W_{\mathrm{et}}$ there
is a canonical bijection

$$
(h_*F)_{\bar v}\;\cong\;
\prod_{\bar w\,|\,\bar v}F_{\bar w},
$$

where the index runs over the finite geometric fibre of $h$ over $\bar v$ and the
$\bar w$-th component is restriction of stalks.

## Proof

The formalisation avoids the strict henselisation: it works with the category of
*split neighbourhoods* of $\bar v$ (pointed etale neighbourhoods $(U,\bar u)$ together
with a decomposition of $W\times_VU$ into pairwise disjoint clopen pieces indexed by the
geometric points $\bar w$ over $\bar v$, the $\bar w$-th piece containing $(\bar u,\bar w)$), shows
that these are cofinal among all pointed etale neighbourhoods (by [lem-fin-finite-splitting]
applied to $h$ there is a split neighbourhood $(V',\bar v')$, and for any pointed etale
neighbourhood $(U,\bar u)$ the base change of its decomposition to $U\times_VV'$ is again one;
Stacks 00UJ applied to an affine chart), that the $\bar w$-th pieces are cofinal among the pointed etale neighbourhoods of
$\bar w$ (an etale-local section lemma for finite algebras with a unique point), and that a
sheaf sends the disjoint clopen cover into a product; finite products commute with the
filtered colimit since the coefficients satisfy AB5. The restriction to geometric points
with algebraically closed residue field suffices for all uses, since these already form a
conservative family (Lemma [lemma-weil-pbc-geometric-stalk-conservative]).

## Detailed form

Let $f:X\to Y$ be finite, let $F$ be an etale sheaf of abelian groups on $X$,
and let $\bar y:\operatorname{Spec}\Omega\to Y$ be a geometric point. If
$\{\bar x\}$ is the finite set of geometric points of $X_{\bar y}$, then

$$
 (f_*F)_{\bar y}\xrightarrow{\sim}
 \prod_{\bar x\in|X_{\bar y}|}F_{\bar x}.
$$

For a finite set, this product is also the direct sum.

## Proof

After base change to the strict henselization at $\bar y$, the finite scheme
$X_{\bar y}$ is the spectrum of a finite algebra over a strictly henselian
local ring, hence a finite disjoint union of strictly henselian local schemes
indexed by the geometric points $\bar x$. Sections over a disjoint union are
the corresponding product of stalks, as computed by the stalk description of
the geometric-stalk convention and the definition of the direct image; for a
finite index set this product is the direct sum.
