+++
id = "lem-weil-pbc-constructible-finite-pushforward-noetherian"
kind = "lemma"
title = "Noetherian finite-pushforward embedding"
order = 1130
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "lem-weil-pbc-constructible-finitely-presented", "lem-weil-pbc-normal-constant-generic"]
+++
Let $U$ be Noetherian and let $C$ be a constructible torsion abelian sheaf on
$U_{\Et}$. There are finite morphisms $h_i:V_i\to U$ and finite abelian groups
$M_i$ with a monomorphism
$C\hookrightarrow\bigoplus_i(h_i)_*\underline{M_i}$.

**Status.** The two sub-gaps this statement used to carry are closed. (a) The
extension of the generic map is valid because the normalization $V$ is normal:
the extension lemma is [lem-weil-pbc-normal-constant-generic]; no locally
constant sheaf is extended across a boundary, the sheaf extended is the
constant sheaf. (b) The factorization of $C\to h_*\underline M$ through one
finite stage is the finite-presentation property of constructible sheaves in
the category of sheaves, [lem-weil-pbc-constructible-finitely-presented],
recorded as the classical input Tag 09Z4.

## Proof

*Step 1: the local model at a point.* For every geometric point $\bar x\to U$,
constructibility gives a finite separable extension $K/\kappa(x)$ and a finite
abelian group $M$ for which $C$ is constant with value $M$ over
$\operatorname{Spec}K$. Let $Z\subset U$ be the reduced closure of $x$, let
$V\to Z$ be the normalization of $Z$ in $K$, and let
$\operatorname{Spec}K\to V$ be the generic inclusion. The scheme $V$ is
integral and normal with function field $K$; this is the classical
normalization of an integral scheme in a finite extension of its function
field (Stacks Project, Morphisms, Lemma 29.54.13, Tag
[035L](https://stacks.math.columbia.edu/tag/035L)).

*Step 2: the generic map.* The identification
$C|_{\operatorname{Spec}K}\cong\underline M$ is a map
$C|_{\operatorname{Spec}K}\to\underline M$, and
[lem-weil-pbc-normal-constant-generic], applied to the normal integral $V$ and
the inclusion $g:\operatorname{Spec}K\to V$ of its generic point, identifies
$g_*\underline M$ with $\underline M$. Hence that map adjoints to
$C|_V\to\underline M$, and adjoints again to a map

$$
 C\longrightarrow h_*\underline M,\qquad h:V\to U
$$

of sheaves on $U$, the morphism $h$ being the composite of the normalization
with $V\to Z\hookrightarrow U$. This is the step that the former pending note
recorded as unjustified: the justification is exactly the normality of $V$,
and no locally constant sheaf is extended across a boundary.

*Step 3: the stalk map at $\bar x$.* Choose a lift $\bar y$ of $\bar x$ to
$V$. The diagram

$$
\begin{array}{ccc}
C_{\bar x}&\xrightarrow{\ \sim\ }&(C|_V)_{\bar y}\\
\downarrow&&\downarrow\\
(h_*\underline M)_{\bar x}&\longrightarrow&\underline M_{\bar y}
\end{array}
$$

is commutative, and $\underline M_{\bar y}=M$, so the stalk map of Step 2 is
injective at $\bar x$.

*Step 4: the finite approximation of $h_*\underline M$.* The normalization map
is integral, not finite in general: writing its affine coordinate algebra as
the filtered union of its finite $\mathcal O_Z$-subalgebras, the induced
direct image is the filtered colimit of the corresponding finite pushforwards,

$$
 h_*\underline M=\varinjlim_i(h_i)_*\underline M,
$$

which over an etale finite-presentation object $W\to U$ is the section formula
$\varinjlim_i\underline M(W\times_UV_i)=\underline M(W\times_UV)$ applied to
the affine limit $V=\varprojlim_iV_i$.

*Step 5: factorization through one finite stage.* The map $C\to h_*\underline
M$ of Step 2 is a morphism from a constructible sheaf into a filtered colimit
of sheaves, so by [lem-weil-pbc-constructible-finitely-presented] it factors
through one stage: there are an index $i$ and a map $C\to(h_i)_*\underline M$
whose composite with the transition map is the given map. Hence $\bar x$
admits a finite pushforward $h_i:V_i\to U$, the morphism $V_i\to Z$ being
finite by construction, detecting its stalk.

*Step 6: finite selection.* The finite-selection statement
[lem-weil-pbc-constructible-noetherian-finite-selection] now produces a finite
set of indices for which the direct sum of the maps of Step 5 is injective on
every geometric stalk; a map of sheaves injective on every geometric stalk is
a monomorphism by conservativity of geometric stalks. This is the Noetherian
construction of Stacks Project, Lemma 59.74.3 (Tag
[09Z6](https://stacks.math.columbia.edu/tag/09Z6)).

*Remark (the Nagata case).* If $U$ is Nagata, for instance of finite type over
a field, the normalization $V\to Z$ is finite already, so Step 4 is
unnecessary and the embedding is produced by Steps 1 to 3 and 6 directly. This
is the case used in the applications below.
