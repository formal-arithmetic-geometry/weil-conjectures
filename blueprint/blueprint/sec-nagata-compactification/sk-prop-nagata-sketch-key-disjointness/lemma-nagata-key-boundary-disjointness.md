+++
id = "lemma-nagata-key-boundary-disjointness"
kind = "lemma"
title = "Prepared boundaries, the comparison boundary, and key disjointness"
order = 272
lean = ["AlgebraicGeometry.TwoOpenSide.KeyDisjoint", "AlgebraicGeometry.TwoOpenSide.admissibleBlowup", "AlgebraicGeometry.TwoOpenSide.isProper_comparisonFst", "AlgebraicGeometry.exists_prepared_keyDisjoint_twoOpenSide", "AlgebraicGeometry.exists_prepared_twoOpenSide"]
uses = ["def-nagata-admissible-blowup", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-dense-compactification", "def-nagata-global-blowup", "def-nagata-graph-extension", "def-nagata-isomorphism-near-closure", "def-nagata-maximal-isomorphism-open", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-separate-constructible-closed", "def-nagata-strict-transform", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-comparison-space", "def-nagata-two-open-dense-compactifications", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-blowup-proper", "lemma-nagata-boundary-disjoint-persists", "lemma-nagata-boundary-loci", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-graph-extension", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-isomorphism-near-closure", "lemma-nagata-maximal-isomorphism-open", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-proper-to-separated-target", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-of-closed-immersion", "lemma-nagata-scheme-image-restrict-open", "lemma-nagata-scheme-image-strict-transform", "lemma-nagata-scheme-image-universal", "lemma-nagata-separate-constructible-closed", "lemma-nagata-strict-transform-closure-characterization", "lemma-nagata-two-open-dense-compactifications", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
Let $X_1,X_2$ be the prepared ambient schemes of
[def-nagata-two-open-prepared-boundaries], with the opens
$U_i\subseteq V_i\subseteq X_i$, the maps $\psi_i\colon V_i\to U$, the
boundary loci $Z_{i,k}$ of [def-nagata-two-open-boundary-loci] and their
closures $\overline Z_{i,k}\subseteq X_i$. Let $V_{12}$, $X_{12}$ and
$p_i\colon X_{12}\to X_i$ be as in
[def-nagata-two-open-comparison-space]. Then, for $\{i,j\}=\{1,2\}$:

1. *(Prepared sides.)* The structural morphism $X_i\to S$ is proper; the
   map $\psi_i$ is proper, extends the inclusion $U_i\hookrightarrow U$,
   satisfies $\psi_i^{-1}(U_i)=U_i$ and is an isomorphism over $U_i$; and
   $\overline Z_{i,1}\cap\overline Z_{i,2}=\varnothing$. All of this
   remains true after any further $V_i$-admissible blow-up of $X_i$, with
   $V_i,U_i,\psi_i,Z_{i,k}$ transported along the isomorphism over $V_i$
   and $\overline Z_{i,k}$ replaced by the closures in the new scheme.
2. *(Comparison projections.)* Both projections $p_i$ are proper. The
   canonical morphism $V_{12}\to p_i^{-1}(V_i)$ is an isomorphism, and
   under it $p_i^{-1}(V_i)\to V_i$ is the base change of
   $\psi_j\colon V_j\to U$ along $\psi_i\colon V_i\to U$. In particular
   $p_1$ is an isomorphism over the open $\psi_1^{-1}(U_2)\subseteq V_1$,
   which contains $Z_{1,2}$.
3. *(Improved comparison.)* Let

   $$
   X_1^{\mathrm{cmp}}=\mathsf{IsoBl}_{V_1,Z_{1,2}}(p_1)\longrightarrow X_1
   $$

   be the construction of [def-nagata-isomorphism-near-closure] applied to
   the proper map $p_1$, the open $V_1$ and the closed subset
   $Z_{1,2}\subseteq V_1$. This is a further $V_1$-admissible blow-up.
   Replace $X_1$ by $X_1^{\mathrm{cmp}}$ (transporting
   $V_1,U_1,\psi_1,Z_{1,k}$, and taking the closures $\overline Z_{1,k}$ in
   $X_1^{\mathrm{cmp}}$), and replace $X_{12}$ and $p_1,p_2$ by the
   comparison space and projections of
   [def-nagata-two-open-comparison-space] formed with $X_1^{\mathrm{cmp}}$;
   this new $X_{12}$ is the strict transform of the old one. For the new
   data, (1) and (2) still hold, and moreover $p_1$ is an isomorphism over
   an open neighbourhood of $\overline Z_{1,2}$ in $X_1$.
4. *(Key disjointness.)* For the improved data of (3), inside
   $X_1\times_SX_2$ one has

   $$
   X_{12}\cap
   (\overline Z_{1,2}\times_S\overline Z_{2,1})
   =\varnothing.
   $$

From now on $X_1$, $X_{12}$ and $p_1,p_2$ always denote the improved data
of (3).

## Proof

**Step 1: the chosen graph extensions.** For each $i$,
[lemma-nagata-graph-extension] says that the replacement
$X_i^{\mathrm{gr}}\to X_i$ of [def-nagata-two-open-graph-extensions] is
$U_i$-admissible and that its associated map $\psi_i$ is proper, extends
$U_i\hookrightarrow U$, has inverse image $\psi_i^{-1}(U_i)=U_i$, and is an
isomorphism there. The structural map of the compactification chosen in
[def-nagata-two-open-dense-compactifications] is proper by
[lemma-nagata-two-open-dense-compactifications], and an admissible blow-up
is proper by [lemma-nagata-blowup-proper]. Their composite, which is the
structural map of $X_i^{\mathrm{gr}}$, is therefore proper.

**Step 2: the prepared boundary closures; proof of (1).** By
[lemma-nagata-boundary-loci], the subsets $Z_{i,i}$ and $Z_{i,j}$ are
disjoint constructible subsets closed in $V_i$. The separation blow-up
$X_i^{\mathrm{prep}}=\mathsf{CSepBl}_{V_i}(Z_{i,i},Z_{i,j})$ of
[def-nagata-two-open-prepared-boundaries] is $V_i$-admissible, so the
selected isomorphism over $V_i$ transports $V_i$, $U_i$ and $\psi_i$
without changing them; the properties of $\psi_i$ from Step 1 therefore
persist. The conclusion of [lemma-nagata-separate-constructible-closed] is
exactly the disjointness of $\overline Z_{i,i}$ and $\overline Z_{i,j}$.
The separation blow-up is proper by [lemma-nagata-blowup-proper];
composing it with the proper morphism $X_i^{\mathrm{gr}}\to S$ of Step 1
proves that $X_i^{\mathrm{prep}}\to S$ is proper. The same two arguments
apply to any further $V_i$-admissible blow-up $b\colon X_i'\to X_i$: it is
proper by [lemma-nagata-blowup-proper], so $X_i'\to S$ is proper; it is an
isomorphism over $V_i$, so it transports $V_i,U_i,\psi_i,Z_{i,k}$
unchanged; and [lemma-nagata-boundary-disjoint-persists] shows that the
new closures remain disjoint. This proves (1).

**Step 3: properness of the comparison projections.** Apply
[lemma-nagata-scheme-image-universal] to $V_{12}\to X_1\times_SX_2$. It
gives the canonical closed immersion
$\iota_{12}\colon X_{12}\hookrightarrow X_1\times_SX_2$ occurring in
[def-nagata-two-open-comparison-space]. The morphism $X_j\to S$ is proper
by (1); hence the projection $\pi_i\colon X_1\times_SX_2\to X_i$ is its
proper base change. The equality $p_i=\pi_i\circ\iota_{12}$ expresses
$p_i$ as a composite of proper morphisms, so $p_i$ is proper.

**Step 4: restriction over $V_i$; proof of (2).** Restrict the
scheme-theoretic image defining $X_{12}$ to the open target
$V_i\times_SX_j\subseteq X_i\times_SX_j$. The inverse image of this open in
$V_{12}$ is all of $V_{12}$, so
[lemma-nagata-scheme-image-restrict-open] identifies $p_i^{-1}(V_i)$ with
the scheme-theoretic image of

$$
V_{12}\longrightarrow V_i\times_SX_j.
$$

The map $V_{12}\to V_i\times_SV_j$ is the pullback of the diagonal
$U\to U\times_SU$; it is therefore a closed immersion because $U\to S$ is
separated. Composing with the open immersion
$V_i\times_SV_j\to V_i\times_SX_j$ shows that the displayed map is an
immersion. It is also proper: its composite to $V_i$ is the base change of
the proper morphism $\psi_j$, while $V_i\times_SX_j\to V_i$ is separated;
apply [lemma-nagata-proper-to-separated-target]. A proper immersion is a
closed immersion, so [lemma-nagata-scheme-image-of-closed-immersion]
identifies its scheme-theoretic image with $V_{12}$ itself. The first
projection of the fibre square $V_{12}=V_1\times_UV_2$ is the displayed
map to $V_i$, and its second component is the map to $V_j$; the universal
property of the fibre product identifies $p_i^{-1}(V_i)\to V_i$ with the
base change of $\psi_j$ along $\psi_i$.

For the last assertion of (2), take $i=1$. By Step 1, $\psi_2$ is an
isomorphism over $U_2$, so the maximal isomorphism open
$N_2=\operatorname{IsoOpen}(\psi_2)$ contains $U_2$ by
[lemma-nagata-maximal-isomorphism-open]; in particular it contains $Z_2$,
whose support $U\setminus U_1$ lies in $U_2$ by
[lemma-nagata-boundary-loci]. Base change along $\psi_1$ shows that
$p_1^{-1}(V_1)\to V_1$ is an isomorphism over
$\psi_1^{-1}(U_2)\subseteq\psi_1^{-1}(N_2)$, and this open contains
$Z_{1,2}=\psi_1^{-1}(Z_2)$. Together with Step 3 this proves (2).

**Step 5: the improved comparison; proof of (3).** The scheme $X_1$ is
proper over the Noetherian scheme $S$, hence Noetherian, so $X_1$ is qcqs
and $V_1$ is a quasi-compact open. The map $p_1$ is proper by Step 3,
$p_1^{-1}(V_1)=V_{12}$ by Step 4, the subset $Z_{1,2}$ is closed in $V_1$ by
[lemma-nagata-boundary-loci], and $p_1^{-1}(V_1)\to V_1$ is an isomorphism
over the open neighbourhood $\psi_1^{-1}(U_2)$ of $Z_{1,2}$ by (2). These
are the hypotheses of [def-nagata-isomorphism-near-closure], and
[lemma-nagata-isomorphism-near-closure] shows that
$X_1^{\mathrm{cmp}}\to X_1$ is $V_1$-admissible and that the strict
transform of $p_1$ is an isomorphism over an open neighbourhood of the
closure of $Z_{1,2}$ in $X_1^{\mathrm{cmp}}$.

The projection of $V_{12}\to X_1\times_SX_2$ to $X_1$ factors through the
open $V_1$, so [lemma-nagata-scheme-image-strict-transform] identifies the
scheme-theoretic image of the lifted map
$V_{12}\to X_1^{\mathrm{cmp}}\times_SX_2$, that is, the comparison space
formed with $X_1^{\mathrm{cmp}}$, with the strict transform of $X_{12}$;
under this identification the new $p_1$ is the strict transform of the old
one. Hence the new $p_1$ is an isomorphism over an open neighbourhood of
the new $\overline Z_{1,2}$. By the last sentence of (1), proved in
Step 2, the new $X_1$ again satisfies (1); $X_2$ is unchanged. Steps 3 and
4 used only (1) for the two sides and the definition of the comparison
space, so they apply verbatim to the new data and give (2). This proves
(3).

**Step 6: the comparison boundary.** Define

$$
Z_{12,2}=(p_1|_{V_{12}})^{-1}(Z_{1,2})\subseteq V_{12}.
$$

Inside $V_{12}$ one has $Z_{12,2}=(p_2|_{V_{12}})^{-1}(Z_{2,2})$. Indeed,
let $z=(v_1,v_2)$ be a point of $V_{12}=V_1\times_UV_2$. The fibre-product
equality gives $\psi_1(v_1)=\psi_2(v_2)=u\in U$. Since
$Z_{1,2}=V_1\times_UZ_2$ and $Z_{2,2}=V_2\times_UZ_2$, membership in either
inverse image is equivalent to $u\in Z_2$. Scheme-theoretically, both sides
are the pullback of the closed subscheme $Z_2\hookrightarrow U$ along the
equal composites $V_{12}\rightrightarrows U$, and the canonical
associativity isomorphisms for fibre products identify the two closed
subschemes. Consequently

$$
p_2(Z_{12,2})\subseteq Z_{2,2}\subseteq\overline Z_{2,2}.
$$

**Step 7: density over the prepared boundary.** Work with the improved data
of (3) and put $C=p_1^{-1}(\overline Z_{1,2})$. Choose an open
neighbourhood $N\subseteq X_1$ of $\overline Z_{1,2}$ over which $p_1$ is
an isomorphism, as supplied by (3). Then $C\subseteq p_1^{-1}(N)$, and the
restriction $C\to\overline Z_{1,2}$ is a homeomorphism (indeed an
isomorphism of the induced reduced subschemes). By Step 4 applied to the
improved data, $p_1^{-1}(V_1)=V_{12}$, so the inverse image of
$Z_{1,2}\subseteq V_1$ under this homeomorphism is $Z_{12,2}$. Since
$Z_{1,2}$ is dense in its closure $\overline Z_{1,2}$, the subset
$Z_{12,2}$ is dense in $C$.

**Step 8: key disjointness; proof of (4).** By Step 6, $Z_{12,2}$ is
contained in the closed subset $p_2^{-1}(\overline Z_{2,2})$ of $X_{12}$.
Because $Z_{12,2}$ is dense in $C$ by Step 7, this closed subset also
contains $C$. Thus $p_2(C)\subseteq\overline Z_{2,2}$. The closed subsets
$\overline Z_{2,2}$ and $\overline Z_{2,1}$ of $X_2$ are disjoint by (1).
Hence no point of $C$ maps into $\overline Z_{2,1}$ under $p_2$. A point of
$X_{12}\cap(\overline Z_{1,2}\times_S\overline Z_{2,1})$ would be a point of
$C$ whose image under $p_2$ lies in $\overline Z_{2,1}$; so the
intersection is empty, which is (4).
