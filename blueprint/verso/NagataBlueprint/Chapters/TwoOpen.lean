import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The two-open compactification theorem" =>

:::group "grp:two-open"
Prepared sides, the comparison space and key boundary disjointness, the intermediate schemes,
the dense-source valuative criterion, and the gluing theorem for a source covered by two
compactifiable opens with dense intersection.
:::

Throughout this chapter $`S` is Noetherian and $`u \colon U \to S` is separated, locally of
finite type and quasi-compact. Let $`O, O'` be opens of $`U`.

# Prepared sides

:::definition "def:two-open-side" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide, AlgebraicGeometry.TwoOpenSide.embX, AlgebraicGeometry.TwoOpenSide.isNoetherian_X")
A _side_ for $`(u, O, O')` consists of a proper morphism $`s \colon X \to S`, an open
$`V \subseteq X`, a proper morphism $`\psi \colon V \to U` over $`S`, and an open immersion
$`\upsilon \colon O \to V` with $`\psi \circ \upsilon = \iota_O`, such that the range of
$`\upsilon` is exactly $`\psi^{-1}O`, $`\psi` is an isomorphism over $`O`, and the composite
$`O \to V \to X` has dense range.
:::

:::definition "def:boundaries" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.selfBoundary, AlgebraicGeometry.TwoOpenSide.forbiddenBoundary, AlgebraicGeometry.TwoOpenSide.Prepared, AlgebraicGeometry.TwoOpenSide.interior, AlgebraicGeometry.TwoOpenSide.interiorEmb")
For a side $`\sigma` put
$$`\overline{Z}_{\mathrm{self}} = \overline{\,\iota_V\bigl(\psi^{-1}(U \setminus O')\bigr)\,}, \qquad \overline{Z}_{\mathrm{forb}} = \overline{\,\iota_V\bigl(\psi^{-1}(U \setminus O)\bigr)\,},`
the _self boundary_ and the _forbidden boundary_, both closed in $`X`. The side is
_prepared_ if
$`\overline{Z}_{\mathrm{self}} \cap \overline{Z}_{\mathrm{forb}} = \emptyset`. The open
complement $`X^{\circ} = X \setminus \overline{Z}_{\mathrm{forb}}` is the _interior_ of the
side; it contains the embedded copy of $`O` {uses "def:two-open-side"}[].
:::

:::proposition "prop:side-transport" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.admissibleBlowup, AlgebraicGeometry.TwoOpenSide.Prepared.admissibleBlowup")
A side may be transported along a $`V`-admissible blow-up of its ambient scheme; boundary
loci transport to their preimages, so preparedness persists {uses "def:boundaries"}[].
:::

:::theorem "thm:prepared-side" (parent := "grp:two-open") (lean := "AlgebraicGeometry.exists_prepared_twoOpenSide")
Let $`O \sqcup O' = U` and assume $`u \circ \iota_O` is compactifiable. Then a prepared side
for $`(u, O, O')` exists.
:::

:::proof "thm:prepared-side" (uses := "thm:dense-compactification, thm:0F3Z, thm:boundary-separation, def:boundaries")
Choose a scheme-theoretically dense compactification of $`u \circ \iota_O`, extend it by the
graph construction, and separate the two boundary closures by the constructible-boundary
separation blow-up.
:::

# The comparison space

Let $`\sigma_1` be a side for $`(u, O_1, O_2)` and $`\sigma_2` a side for
$`(u, O_2, O_1)`, with ambient schemes $`X_1, X_2` and proper extensions
$`\psi_1, \psi_2`.

:::definition "def:comparison-space" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.comparisonMap, AlgebraicGeometry.TwoOpenSide.comparisonSpace, AlgebraicGeometry.TwoOpenSide.comparisonFst, AlgebraicGeometry.TwoOpenSide.comparisonSnd, AlgebraicGeometry.TwoOpenSide.isProper_comparisonFst, AlgebraicGeometry.TwoOpenSide.isProper_comparisonSnd")
The _comparison morphism_ is the canonical morphism $`V_1 \times_U V_2 \to X_1 \times_S X_2`.
The _comparison space_ $`X_{12}` is its scheme-theoretic image, with the two projections
$`\mathrm{pr}_1 \colon X_{12} \to X_1` and $`\mathrm{pr}_2 \colon X_{12} \to X_2`, both
proper {uses "def:two-open-side"}[].
:::

:::definition "def:key-disjoint" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.KeyDisjoint, AlgebraicGeometry.TwoOpenSide.comparisonBoundary, AlgebraicGeometry.TwoOpenSide.keyDisjoint_of_comparisonBoundary_subset, AlgebraicGeometry.TwoOpenSide.keyDisjoint_of_dense_comparisonBoundary")
The pair $`(\sigma_1, \sigma_2)` satisfies _key boundary disjointness_ if no point of
$`X_{12}` projects into the forbidden boundary on both sides:
$$`X_{12} \cap \bigl(\overline{Z}_{1,\mathrm{forb}} \times_S \overline{Z}_{2,\mathrm{forb}}\bigr) = \emptyset.`
The _comparison boundary_ is
$`\mathrm{pr}_1^{-1}\overline{Z}_{1,\mathrm{forb}}`; key disjointness says that its image
under $`\mathrm{pr}_2` avoids $`\overline{Z}_{2,\mathrm{forb}}`
{uses "def:comparison-space"}[] {uses "def:boundaries"}[].
:::

:::lemma_ "lem:key-disjoint-avoids" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.KeyDisjoint.avoids")
Key boundary disjointness implies that, for any pair of valuation-ring extensions of a common
generic point of $`O_1 \cap O_2` to the two ambient models, at least one of the two avoids its
forbidden boundary.
:::

:::theorem "thm:improved-comparison" (parent := "grp:two-open") (lean := "AlgebraicGeometry.exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary, AlgebraicGeometry.TwoOpenSide.injOn_comparisonFst_admissibleBlowup, AlgebraicGeometry.TwoOpenSide.blowupComparison, AlgebraicGeometry.TwoOpenSide.improvedToStrictTransform, AlgebraicGeometry.TwoOpenSide.isoOpen, AlgebraicGeometry.TwoOpenSide.isIso_comparisonFst_restrict_isoOpen, AlgebraicGeometry.TwoOpenSide.comparisonBoundary_subset_preimage_selfBoundary")
Given prepared sides $`\sigma_1, \sigma_2` with $`O_1 \sqcup O_2 = U`, there is a
$`V_1`-admissible blow-up of $`X_1` after which the comparison boundary of the improved pair
is contained in the preimage of the self boundary of $`\sigma_1`.
:::

:::proof "thm:improved-comparison" (uses := "def:key-disjoint, prop:side-transport, thm:0F3W, def:strict-transform")
Four ingredients enter. First, over the proper-extension open $`V_1` the comparison space is
the fibre product $`V_1 \times_U V_2` itself: the comparison morphism is an immersion, being
the base change of the diagonal of $`u` followed by an open immersion, and it is proper over
$`V_1`, so its range is closed there. Second, the first comparison projection is an
isomorphism over the image in $`X_1` of the locus of $`V_1` lying above $`O_2`; indeed
$`\psi_2` is an isomorphism over $`O_2` and, over $`V_1`, the first projection is its base
change. That open contains the forbidden boundary of $`\sigma_1`, because
$`U \setminus O_1 \subseteq O_2`. Third, after a $`V_1`-admissible blow-up the comparison
space of the improved pair is a closed subscheme of the strict transform of the old
comparison space, so the improved first projection is injective wherever the
strict-transform projection is an isomorphism; this is where the isomorphism near a boundary
closure enters. Fourth, a density criterion: controlling the second projection on a subset
whose closure swallows the comparison boundary suffices, because the self boundary is itself
a closure.
:::

:::theorem "thm:two-open-preparation" (parent := "grp:two-open") (lean := "AlgebraicGeometry.exists_prepared_keyDisjoint_twoOpenSide, AlgebraicGeometry.TwoOpenPreparation, AlgebraicGeometry.nonempty_twoOpenPreparation")
Let $`O_1 \sqcup O_2 = U` and assume both $`u \circ \iota_{O_1}` and $`u \circ \iota_{O_2}`
are compactifiable. Then there exist prepared sides $`\sigma_1` for $`(u, O_1, O_2)` and
$`\sigma_2` for $`(u, O_2, O_1)` satisfying key boundary disjointness.
:::

:::proof "thm:two-open-preparation" (uses := "thm:prepared-side, thm:improved-comparison, def:key-disjoint")
Take prepared sides on both sides, improve the first, and observe that a comparison boundary
landing in the self boundary of a _prepared_ second side cannot meet its forbidden boundary.
:::

# The intermediate schemes and the theorem

:::definition "def:intermediate" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.intermediate, AlgebraicGeometry.TwoOpenSide.intermediateU, AlgebraicGeometry.TwoOpenSide.intermediateInterior, AlgebraicGeometry.TwoOpenSide.intermediateHom")
For a side $`\sigma` with interior $`X^{\circ}`, the _intermediate scheme_ is the pushout
$$`W \;=\; U \ \sqcup_{O}\ X^{\circ},`
the gluing of $`U` and $`X^{\circ}` along the embedded copy of $`O`, with its two chart open
immersions and its structure morphism $`W \to S` {uses "def:boundaries"}[].
:::

:::proposition "prop:intermediate" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.graph, AlgebraicGeometry.TwoOpenSide.isProper_graph, AlgebraicGeometry.TwoOpenSide.intermediateGraph, AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph, AlgebraicGeometry.TwoOpenSide.isSeparated_intermediateHom, AlgebraicGeometry.TwoOpenSide.locallyOfFiniteType_intermediateHom, AlgebraicGeometry.TwoOpenSide.dense_range_intermediateU, AlgebraicGeometry.TwoOpenSide.compactSpace_intermediate, AlgebraicGeometry.TwoOpenSide.isNoetherian_intermediate")
* The overlap morphism $`O \to U \times_S X^{\circ}` is a closed immersion: its range is the
  preimage of the closed range of the proper graph $`V \to U \times_S X`, and the range of the
  embedding of $`O` in $`V` is exactly $`\psi^{-1}O`.
* Consequently $`W \to S` is separated: a morphism out of a scheme covered by two opens is
  separated as soon as the overlap morphism into the product of the two charts over the base
  is a closed immersion.
* The copy of $`U` is dense in $`W`, and $`W` is Noetherian over $`S`.
:::

:::definition "def:dense-valuative" (parent := "grp:two-open") (lean := "AlgebraicGeometry.ValuativeCommSqWithPt, AlgebraicGeometry.ValuativeCommSqWithPt.ofSpecializes, AlgebraicGeometry.ValuativeCommSqWithPt.ofIsDominant, AlgebraicGeometry.ValuativeCriterion.RelativeTo, AlgebraicGeometry.ValuativeCriterion.RelativeTo.existsUnique, AlgebraicGeometry.ValuativeCriterion.RelativeTo.of_existsUnique, AlgebraicGeometry.ValuativeCriterion.RelativeTo.restrict, AlgebraicGeometry.ValuativeCriterion.RelativeTo.toImage")
The _valuative criterion relative to a morphism_ $`h \colon U \to X` asks for unique lifting
only in those valuative squares for $`f \colon X \to S` whose generic point factors through
$`h`.
:::

:::theorem "thm:dense-valuative-criterion" (parent := "grp:two-open") (lean := "AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion_of_isDominant, AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant, AlgebraicGeometry.ValuativeCriterion.RelativeTo.existence_of_isSchemeTheoreticallyDominant, AlgebraicGeometry.ValuativeCriterion.RelativeTo.existence_of_isDominant, AlgebraicGeometry.ValuativeCriterion.RelativeTo.existence_of_isSchemeTheoreticallyDominant_of_isAffine, AlgebraicGeometry.exists_stalkClosedPointTo_of_generic_eq, AlgebraicGeometry.exists_flat_polynomial_presentation")
Let $`f \colon X \to S` be a morphism and $`h \colon U \to X` quasi-compact and dominant. If
every valuative square for $`f` whose generic point factors through $`h` admits a unique
lift, then $`f` is universally closed; the corresponding statement for uniqueness gives
separatedness. Moreover, for a scheme-theoretically dominant quasi-compact morphism and a
point of its scheme-theoretic image, a valuation probe centred at that point exists
{uses "def:dense-valuative"}[].
:::

:::theorem "thm:two-open" (parent := "grp:two-open") (lean := "AlgebraicGeometry.HasCompactification.of_two_open_cover")
Let $`S` be Noetherian and let $`u \colon U \to S` be separated, locally of finite type and
quasi-compact. Suppose $`U` is covered by two opens $`O_1, O_2` whose intersection
$`O_1 \cap O_2` is dense in $`U`, and suppose that both $`u \circ \iota_{O_1}` and
$`u \circ \iota_{O_2}` admit compactifications. Then $`u` admits a compactification.
:::

:::proof "thm:two-open" (uses := "thm:two-open-preparation, def:intermediate, prop:intermediate, thm:0F3X, thm:admissible-density, lem:key-disjoint-avoids, thm:dense-valuative-criterion, def:compactification")
Take a key-disjoint prepared pair and form the two intermediate schemes $`W_1, W_2`; they are
separated, of finite type and Noetherian over $`S`, and each contains a dense copy of $`U`.
Apply the existence of common modifications to $`W_1, W_2` and their common copy of $`U`; let
$`W` be the resulting common modification. Density of $`O_1 \cap O_2` transports through the
finite modification diagram, so $`O_1 \cap O_2` is dense in $`W`. Every valuative square
through this dense source lifts uniquely: extend the generic point to the two proper sides,
pass to the side which avoids its forbidden boundary, and lift along the proper admissible
blow-up. The dense-source valuative criterion then shows that $`W \to S` is universally
closed, hence proper, and $`U \to W` is an open immersion; this is a compactification of
$`u`.
:::
