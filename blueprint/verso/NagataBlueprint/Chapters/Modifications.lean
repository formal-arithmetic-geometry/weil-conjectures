import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Modifications" =>

:::group "grp:modifications"
Elimination of indeterminacy and its consumers: transport of scheme-theoretic images,
common modifications, graph extensions, isomorphism near a boundary closure, and the
boundary preparation used by the two-open theorem.
:::

:::theorem "thm:081S" (parent := "grp:modifications") (lean := "AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap")
Let $`X` be quasi-compact quasi-separated, let $`U \subseteq X` be a quasi-compact open and
let $`q \colon Z \to X` be separated, locally of finite type and quasi-compact. Assume $`q`
restricts to an isomorphism over $`U`. Then there is a $`U`-admissible centre $`\sI` on $`X`
such that the strict transform of $`q` along $`\pi_\sI`, preserving $`\mathrm{pr}(\sI)`, is
an open immersion into $`\Bl_\sI(X)`.
:::

:::proof "thm:081S" (uses := "thm:01PH, thm:admissible-density, cor:conrad25, cor:080L, def:strict-transform, lem:kernel-criterion")
First prepare the boundary: blow up a finite-type ideal whose support is exactly
$`X \setminus U`, so that $`U` becomes scheme-theoretically dense. Next extend the inverse of
$`q` over $`U` to a section over an open $`W` of a second admissible blow-up. Compose the two
blow-ups. Finally, the graph of the extension is closed and contains the schematically dense
$`U`-graph, so it cuts out the strict transform, which is therefore isomorphic to the open
$`W`.

This route replaces the classical derivation from module flattening: the surveyed material
contains no flattening theorem, and none is needed.
:::

:::theorem "thm:0F3Y" (parent := "grp:modifications") (lean := "AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup")
Let $`\sI` be a $`U`-admissible centre on $`X`. Let $`h` be a quasi-compact morphism into a
fibre product over $`X` whose first component lands in $`U`, and let $`h'` be a lift of $`h`
along the base change of $`\pi_\sI`. Then the scheme-theoretic image of $`h'` is the strict
transform of the scheme-theoretic image of $`h`: the kernel of $`h'` equals the kernel of the
projection to the blown-up fibre product of the strict transform of $`\iota_{\operatorname{im} h}`
along the base change of $`\pi_\sI`, preserving the preimage of the preserved open.
:::

:::proof "thm:0F3Y" (uses := "def:strict-transform, lem:kernel-criterion, thm:admissible-density")
Both kernels are computed from the same schematically dense open locus over $`U`.
:::

:::definition "def:common-modification" (parent := "grp:modifications") (lean := "AlgebraicGeometry.CommonModification")
Let $`s_1 \colon X_1 \to S`, $`s_2 \colon X_2 \to S` be morphisms and let
$`j_1 \colon U \to X_1`, $`j_2 \colon U \to X_2` be open immersions with
$`s_1 \circ j_1 = s_2 \circ j_2`. A _common modification_ consists of $`j_i(U)`-admissible
centres $`\sI_i` on $`X_i`, a scheme $`W` with a morphism $`w \colon W \to S`, open
immersions $`k_i \colon \Bl_{\sI_i}(X_i) \to W` over $`S` whose ranges cover $`W`, and lifts
$`u_i \colon U \to \Bl_{\sI_i}(X_i)` of $`j_i` with $`k_1 \circ u_1 = k_2 \circ u_2`, such
that $`w` is separated, locally of finite type and quasi-compact
{uses "def:admissible"}[].
:::

:::theorem "thm:0F3X" (parent := "grp:modifications") (lean := "AlgebraicGeometry.nonempty_commonModification")
Let $`S` be quasi-compact quasi-separated, let $`s_1 \colon X_1 \to S` and
$`s_2 \colon X_2 \to S` be separated, locally of finite type and quasi-compact, and let
$`j_1 \colon U \to X_1`, $`j_2 \colon U \to X_2` be quasi-compact open immersions with
$`s_1 \circ j_1 = s_2 \circ j_2`. Then a common modification of $`(s_1, s_2, j_1, j_2)`
exists.
:::

:::proof "thm:0F3X" (uses := "def:common-modification, thm:081S, thm:080E, thm:080M, cor:080L")
Form the graph $`\gamma = (j_1, j_2) \colon U \to X_1 \times_S X_2`, let $`X_{12}` be its
scheme-theoretic image and let $`p_1, p_2` be the two projections of $`X_{12}`. Both are
isomorphisms over $`U`, so elimination of indeterminacy applies to each: after admissible
blow-ups of $`X_1` and $`X_2`, the strict transforms of $`p_1` and $`p_2` become open
immersions. These strict transforms are blow-ups of $`X_{12}` at the pulled-back centres; the
product of the two pulled-back centres dominates both, and the resulting blow-up of
$`X_{12}` sits, as an open subscheme, inside a single admissible blow-up of each $`X_i`.
Gluing the two blow-ups along that common open produces $`W`, which is separated, locally of
finite type and quasi-compact over $`S`.
:::

:::definition "def:proper-extension" (parent := "grp:modifications") (lean := "AlgebraicGeometry.Compactification.ProperExtension")
Let $`u \colon U \to S` be a morphism, $`V \subseteq U` a quasi-compact open and
$`c = (Z, g, i)` a compactification of $`u \circ \iota_V` {uses "def:compactification"}[]. A
_graph extension_ of $`c` consists of an $`i(V)`-admissible centre on $`Z`, an open
$`V^{\mathrm{gr}}` of the blow-up and a proper morphism $`\psi \colon V^{\mathrm{gr}} \to U`
over $`S` extending the inclusion of $`V`, such that $`V` embeds in $`V^{\mathrm{gr}}` as
exactly the preimage $`\psi^{-1}V` and $`\psi` is an isomorphism over $`V`.
:::

:::theorem "thm:0F3Z" (parent := "grp:modifications") (lean := "AlgebraicGeometry.Compactification.nonempty_properExtension")
Let $`S` be quasi-compact quasi-separated, let $`u \colon U \to S` be separated, locally of
finite type and quasi-compact, let $`V \subseteq U` be a quasi-compact open and let $`c` be a
compactification of $`u \circ \iota_V`. Then a graph extension of $`c` exists.
:::

:::proof "thm:0F3Z" (uses := "def:proper-extension, thm:0F3Y, thm:081S")
Take the graph $`\gamma = (i, \iota_V) \colon V \to Z \times_S U`, a partial section of the
first projection over the open immersion $`i`. Its scheme-theoretic image is transported
through an admissible blow-up, and elimination of indeterminacy makes the corresponding
strict transform an open immersion; $`V^{\mathrm{gr}}` is that open, and $`\psi` is the
second projection, proper because $`Z \times_S U \to U` is proper.
:::

:::theorem "thm:0F3W" (parent := "grp:modifications") (lean := "AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure")
Let $`X` be quasi-compact quasi-separated, let $`U \subseteq X` be a quasi-compact open and
let $`q \colon Z \to X` be proper. Let $`T \subseteq U` be a subset which is closed in $`U`
and let $`N \subseteq X` be an open containing $`T` over which $`q` is an isomorphism. Then
there are a $`U`-admissible centre $`\sI` on $`X` and an open $`N' \subseteq \Bl_\sI(X)` with
$`\overline{\pi_\sI^{-1}T} \subseteq N'` such that the strict transform of $`q` along
$`\pi_\sI` is an isomorphism over $`N'`.
:::

:::proof "thm:0F3W" (uses := "thm:081S, thm:0F3V, def:strict-transform")
Separate the boundary pieces by a separation blow-up and apply elimination of indeterminacy
over the resulting neighbourhood.
:::

# Boundary preparation

:::theorem "thm:dense-compactification" (parent := "grp:modifications") (lean := "AlgebraicGeometry.Compactification.denseRefinement, AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_denseRefinement_i, AlgebraicGeometry.exists_compactification_isSchemeTheoreticallyDominant")
Every compactification of a quasi-compact morphism may be replaced by one whose open
immersion is scheme-theoretically dominant, namely by passing to the scheme-theoretic image
of the open immersion inside the ambient scheme {uses "def:compactification"}[].
:::

:::theorem "thm:boundary-separation" (parent := "grp:modifications") (lean := "AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures")
If $`T_1, T_2` are disjoint closed subsets of a quasi-compact open $`U` of a quasi-compact
quasi-separated scheme $`X` with quasi-compact complements in $`U`, then after a
$`U`-admissible blow-up of $`X` the closures of the inverse images of $`T_1` and $`T_2` are
disjoint.
:::

:::proof "thm:boundary-separation" (uses := "thm:0F3V, thm:01PH, prop:strict-transform-basic")
Cut out $`T_1` and $`T_2` by finite-type ideal sheaves and blow up their sum; the strict
transforms of the two closed subschemes are then disjoint, and each contains the closure of
the inverse image of the corresponding closed subset.
:::
