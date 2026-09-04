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

:::definition "def:two-open-side" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide")
*A side of the two-open compactification theorem.*
A _side_ for $`(u, O)` consists of a proper morphism $`s \colon X \to S`, an open
$`V \subseteq X`, a proper morphism $`\psi \colon V \to U` over $`S`, and an open immersion
$`\upsilon \colon O \to V` with $`\psi \circ \upsilon = \iota_O`, such that the range of
$`\upsilon` is exactly $`\psi^{-1}O`, $`\psi` is an isomorphism over $`O`, and the composite
$`O \to V \to X` has dense range. The second open $`O'` does not enter this data; it is a
parameter of the boundary loci below.
:::

:::definition "def:boundaries" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.selfBoundary, AlgebraicGeometry.TwoOpenSide.forbiddenBoundary, AlgebraicGeometry.TwoOpenSide.Prepared, AlgebraicGeometry.TwoOpenSide.interior")
*The self boundary, the forbidden boundary and preparedness.*
For a side $`\sigma` and an open $`O'` of $`U` put
$$`\overline{Z}_{\mathrm{self}} = \overline{\,\iota_V\bigl(\psi^{-1}(U \setminus O')\bigr)\,}, \qquad \overline{Z}_{\mathrm{forb}} = \overline{\,\iota_V\bigl(\psi^{-1}(U \setminus O)\bigr)\,},`
the _self boundary_ relative to $`O'` and the _forbidden boundary_, both closed in $`X`.
Only the self boundary depends on $`O'`. The side is _prepared_ relative to $`O'` if
$`\overline{Z}_{\mathrm{self}} \cap \overline{Z}_{\mathrm{forb}} = \emptyset`. The open
complement $`X^{\circ} = X \setminus \overline{Z}_{\mathrm{forb}}` is the _interior_ of the
side {uses "def:two-open-side"}[].
:::

:::lemma_ "lem:interior-contains-copy" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.range_embX_subset_interior")
*The interior contains the embedded copy of the open.*
The interior of a side contains the embedded copy of $`O` in the ambient scheme
{uses "def:boundaries"}[].
:::

:::proof "lem:interior-contains-copy" (uses := "def:boundaries, def:two-open-side")
The embedded copy of $`O` is the part of $`V` lying over $`O`, which is disjoint from the
inverse image of $`U \setminus O`; being open, it is also disjoint from its closure, the
forbidden boundary.
:::

:::proposition "prop:side-transport" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.admissibleBlowup, AlgebraicGeometry.TwoOpenSide.Prepared.admissibleBlowup")
*Transport of a side along an admissible blow-up.*
Let $`S` be Noetherian. A side may be transported along a $`V`-admissible blow-up of its
ambient scheme; boundary loci transport to their preimages, so preparedness relative to
any $`O'` persists
{uses "def:boundaries"}[].
:::

:::proof "prop:side-transport" (uses := "def:two-open-side, def:boundaries, def:admissible, prop:admissible-basic, thm:admissible-density")
Let $`\sigma = (s, V, \psi, \upsilon)` be a side and let $`\sI` be a $`V`-admissible centre on
its ambient scheme $`X`, with blow-up $`\pi \colon \Bl_\sI(X) \to X`. The transported side has
ambient scheme $`\Bl_\sI(X)`, structure morphism $`\pi \circ s`, which is proper because both
factors are; open $`V' = \pi^{-1}V`; proper extension $`\psi' = \psi \circ \pi|_{V'}`; and
embedding $`\upsilon' = (\pi|_{V'})^{-1} \circ \upsilon`. Here $`\pi|_{V'} \colon V' \to V` is
an isomorphism, $`\sI` being $`V`-admissible, so $`\psi'` is proper and $`\upsilon'` is an
open immersion with $`\psi' \circ \upsilon' = \psi \circ \upsilon = \iota_O`. Transporting
along an isomorphism also gives the two remaining conditions on the range: the range of
$`\upsilon'` is the inverse image under $`\pi|_{V'}` of the range of $`\upsilon`, that is of
$`\psi^{-1}O`, which is $`\psi'^{-1}O`; and $`\psi'` is an isomorphism over $`O` because
$`\psi` is.

Density of the composite $`O \to V' \to \Bl_\sI(X)` is the only point where the blow-up itself
is used. Since $`\pi` is an isomorphism over the open $`V`, which contains the range of
$`O \to V \to X`, the range of the transported composite is exactly the inverse image under
$`\pi` of that range. The latter is dense in $`X`, and $`X` is Noetherian, hence quasi-compact
quasi-separated, so its inverse image under the admissible blow-up is dense in $`\Bl_\sI(X)`.

For the boundary loci, the square formed by $`\pi|_{V'}`, the two open inclusions of $`V'` and
$`V` and $`\pi` commutes, and $`\pi|_{V'}` is an isomorphism; therefore, for every subset
$`A \subseteq U`,
$$`\iota_{V'}\bigl(\psi'^{-1}A\bigr) \;=\; \pi^{-1}\bigl(\iota_V(\psi^{-1}A)\bigr).`
Taking $`A = U \setminus O'` and $`A = U \setminus O` shows that the self and forbidden
boundaries of the transported side are the closures of the inverse images under $`\pi` of the
sets whose closures are the self and forbidden boundaries of $`\sigma`.

Preparedness now persists. For any $`A \subseteq X` one has
$`\overline{\pi^{-1}A} \subseteq \pi^{-1}\overline{A}`, the right-hand side being a closed set
containing $`\pi^{-1}A` by continuity of $`\pi`. So each transported boundary closure is
contained in the inverse image of the corresponding boundary closure of $`\sigma`; those two
inverse images are disjoint because $`\overline{Z}_{\mathrm{self}}` and
$`\overline{Z}_{\mathrm{forb}}` are, and inverse images preserve disjointness. Hence the two
transported boundary closures are disjoint, for any choice of $`O'`.
:::

:::theorem "thm:prepared-side" (parent := "grp:two-open") (lean := "AlgebraicGeometry.exists_prepared_twoOpenSide")
*Existence of a prepared side.*
Let $`S` be Noetherian, let $`u \colon U \to S` be separated, locally of finite type and
quasi-compact, let $`O \sqcup O' = U` and assume $`u \circ \iota_O` is compactifiable. Then a
side for $`(u, O)` which is prepared relative to $`O'` exists.
:::

:::proof "thm:prepared-side" (uses := "thm:dense-compactification, thm:0F3Z, thm:boundary-separation, def:boundaries")
Choose a scheme-theoretically dense compactification of $`u \circ \iota_O`, extend it by the
graph construction, and separate the two boundary closures by the constructible-boundary
separation blow-up.
:::

# The comparison space

Let $`\sigma_1` be a side for $`(u, O_1)` and $`\sigma_2` a side for $`(u, O_2)`, with
ambient schemes $`X_1, X_2` and proper extensions $`\psi_1, \psi_2`. Self boundaries are
taken relative to the other open: $`\overline{Z}_{1,\mathrm{self}}` relative to $`O_2` and
$`\overline{Z}_{2,\mathrm{self}}` relative to $`O_1`.

:::definition "def:comparison-space" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.comparisonMap, AlgebraicGeometry.TwoOpenSide.comparisonSpace, AlgebraicGeometry.TwoOpenSide.comparisonFst, AlgebraicGeometry.TwoOpenSide.comparisonSnd")
*The comparison space.*
The _comparison morphism_ is the canonical morphism $`V_1 \times_U V_2 \to X_1 \times_S X_2`.
The _comparison space_ $`X_{12}` is its scheme-theoretic image, with the two projections
$`\mathrm{pr}_1 \colon X_{12} \to X_1` and $`\mathrm{pr}_2 \colon X_{12} \to X_2`
{uses "def:two-open-side"}[].
:::

:::lemma_ "lem:comparison-projections-proper" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.isProper_comparisonFst, AlgebraicGeometry.TwoOpenSide.isProper_comparisonSnd")
*Properness of the comparison projections.*
Both projections $`\mathrm{pr}_1 \colon X_{12} \to X_1` and
$`\mathrm{pr}_2 \colon X_{12} \to X_2` of the comparison space are proper
{uses "def:comparison-space"}[].
:::

:::proof "lem:comparison-projections-proper" (uses := "def:comparison-space, def:two-open-side")
Each projection is the closed immersion of the comparison space into $`X_1 \times_S X_2`
followed by a projection of the product, which is a base change of the proper structure
morphism of the other ambient model.
:::

:::definition "def:key-disjoint" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.KeyDisjoint, AlgebraicGeometry.TwoOpenSide.comparisonBoundary")
*Key boundary disjointness.*
The pair $`(\sigma_1, \sigma_2)` satisfies _key boundary disjointness_ if no point of
$`X_{12}` projects into the forbidden boundary on both sides:
$$`X_{12} \cap \bigl(\overline{Z}_{1,\mathrm{forb}} \times_S \overline{Z}_{2,\mathrm{forb}}\bigr) = \emptyset.`
The _comparison boundary_ is
$`\mathrm{pr}_1^{-1}\overline{Z}_{1,\mathrm{forb}}`; key disjointness says that its image
under $`\mathrm{pr}_2` avoids $`\overline{Z}_{2,\mathrm{forb}}`
{uses "def:comparison-space"}[] {uses "def:boundaries"}[].
:::

:::lemma_ "lem:key-disjoint-avoids" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.KeyDisjoint.avoids")
*One valuation extension avoids its forbidden boundary.*
Key boundary disjointness implies that, for any pair of valuation-ring extensions of a common
generic point of $`O_1 \cap O_2` to the two ambient models, at least one of the two avoids its
forbidden boundary.
:::

:::theorem "thm:improved-comparison" (parent := "grp:two-open") (lean := "AlgebraicGeometry.exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary")
*The improved comparison.*
Let $`S` be Noetherian and let $`u \colon U \to S` be separated, locally of finite type and
quasi-compact. Given sides $`\sigma_1` for $`(u, O_1)` and $`\sigma_2` for $`(u, O_2)`
with $`O_1 \sqcup O_2 = U`, there is a $`V_1`-admissible blow-up of $`X_1`
after which the comparison boundary of the improved pair is contained in the preimage of the
self boundary of $`\sigma_2`. No preparedness of the two sides is needed.
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

:::theorem "thm:two-open-preparation" (parent := "grp:two-open") (lean := "AlgebraicGeometry.exists_prepared_keyDisjoint_twoOpenSide")
*Existence of a prepared, key-disjoint pair of sides.*
Let $`S` be Noetherian, let $`u \colon U \to S` be separated, locally of finite type and
quasi-compact, let $`O_1 \sqcup O_2 = U` and assume both $`u \circ \iota_{O_1}` and
$`u \circ \iota_{O_2}` are compactifiable. Then there exist sides $`\sigma_1` for
$`(u, O_1)`, prepared relative to $`O_2`, and $`\sigma_2` for $`(u, O_2)`, prepared relative
to $`O_1`, satisfying key boundary disjointness.
:::

:::proof "thm:two-open-preparation" (uses := "thm:prepared-side, thm:improved-comparison, def:key-disjoint")
Take prepared sides on both sides, improve the first, and observe that a comparison boundary
landing in the self boundary of a _prepared_ second side cannot meet its forbidden boundary.
:::

# The intermediate schemes and the theorem

:::definition "def:intermediate" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.intermediate, AlgebraicGeometry.TwoOpenSide.intermediateU, AlgebraicGeometry.TwoOpenSide.intermediateInterior, AlgebraicGeometry.TwoOpenSide.intermediateHom, AlgebraicGeometry.TwoOpenSide.graph, AlgebraicGeometry.TwoOpenSide.intermediateGraph")
*The intermediate scheme.*
For a side $`\sigma` with interior $`X^{\circ}`, the _intermediate scheme_ is the pushout
$$`W \;=\; U \ \sqcup_{O}\ X^{\circ},`
the gluing of $`U` and $`X^{\circ}` along the embedded copy of $`O`, with its two chart open
immersions and its structure morphism $`W \to S`. We write $`\gamma \colon V \to U \times_S X`
for the _graph_ of the proper extension $`\psi` and
$`O \to U \times_S X^{\circ}` for the _overlap morphism_ of the two charts
{uses "def:boundaries"}[].
:::

:::proposition "prop:intermediate" (parent := "grp:two-open") (lean := "AlgebraicGeometry.TwoOpenSide.isProper_graph, AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph, AlgebraicGeometry.TwoOpenSide.isSeparated_intermediateHom, AlgebraicGeometry.TwoOpenSide.dense_range_intermediateU, AlgebraicGeometry.TwoOpenSide.isNoetherian_intermediate")
*Properties of the intermediate scheme.*
Let $`\sigma` be a side {uses "def:intermediate"}[].

* The graph $`\gamma \colon V \to U \times_S X` is proper; in particular its range is closed.
* The overlap morphism $`O \to U \times_S X^{\circ}` is a closed immersion: its range is the
  preimage of the closed range of $`\gamma`, and the range of the embedding of $`O` in $`V`
  is exactly $`\psi^{-1}O`.
* If $`u` is separated, then so is $`W \to S`: a morphism out of a scheme covered by two
  opens is separated as soon as the overlap morphism into the product of the two charts over
  the base is a closed immersion.
* The copy of $`U` is dense in $`W`; and if $`S` is Noetherian and $`u` is locally of finite
  type and quasi-compact, then $`W` is Noetherian.
:::

:::proof "prop:intermediate" (uses := "def:intermediate, def:two-open-side, def:boundaries, lem:interior-contains-copy")
The graph is proper by cancellation. Its composite with the first projection
$`U \times_S X \to U` is the proper morphism $`\psi`, and that projection is a base change of
the proper structure morphism $`s \colon X \to S`, hence separated; a composite which is
proper with a separated second factor has a proper first factor. Properness gives closed
range.

For the overlap morphism, work over the interior. Its range is the inverse image in
$`U \times_S X^{\circ}` of the range of $`\gamma`: over the complement of the forbidden
boundary the graph passes through the embedded copy of $`O` exactly over $`O`, because the
range of $`\upsilon` is precisely $`\psi^{-1}O`. That inverse image is closed, the range of
$`\gamma` being closed; and the overlap morphism is an immersion, being a morphism out of an
open subscheme with a section-like description on each factor. An immersion with closed range
is a closed immersion.

Separatedness of $`W \to S` is then the two-open criterion (Stacks Project Tag 0F3U): $`W` is
covered by its two charts $`U` and $`X^{\circ}`; each is separated over $`S`, the first
because $`u` is separated and the second because $`X^{\circ}` is an open of $`X` and $`s` is
proper, hence separated; and the overlap morphism into the product $`U \times_S X^{\circ}` of
the two charts over the base is a closed immersion by the previous item. A morphism out of a
scheme covered by two opens is separated as soon as that overlap morphism is a closed
immersion.

Density: the two charts cover $`W`, so it suffices to see that the copy of $`U` meets every
nonempty open of the second chart. The composite $`O \to V \to X` has dense range by the
definition of a side, and this embedded copy of $`O` lies inside the interior $`X^{\circ}`,
so it is dense there; it lies inside the copy of $`U` in $`W`, since the two charts are glued
precisely along it. Hence the copy of $`U` is dense in $`W`.

Finally, assume $`S` Noetherian and $`u` locally of finite type and quasi-compact. Then $`U`
is a Noetherian scheme, and so is $`X`, being proper — in particular locally of finite type
and quasi-compact — over $`S`; the interior $`X^{\circ}` is an open subscheme of $`X`, hence
Noetherian as well. A scheme covered by two Noetherian opens is Noetherian, so $`W` is
Noetherian.
:::

:::definition "def:dense-valuative" (parent := "grp:two-open") (lean := "AlgebraicGeometry.ValuativeCriterion.RelativeTo")
*The valuative criterion relative to a morphism.*
The _valuative criterion relative to a morphism_ $`h \colon U \to X` asks for unique lifting
only in those valuative squares for $`f \colon X \to S` whose generic point factors through
$`h`.
:::

:::theorem "thm:dense-valuative-criterion" (parent := "grp:two-open") (lean := "AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion_of_isDominant, AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant, AlgebraicGeometry.ValuativeCommSqWithPt.ofIsDominant")
*The dense-source valuative criterion.*
Let $`f \colon X \to S` be a morphism and $`h \colon U \to X` quasi-compact and dominant. If
every valuative square for $`f` whose generic point factors through $`h` admits a unique
lift, then $`f` is universally closed; the corresponding statement for uniqueness gives
separatedness, $`f` being assumed quasi-separated. Moreover, for a quasi-compact dominant
morphism $`h` and any point $`z` of its target, a valuation probe for $`h` centred at $`z`
exists {uses "def:dense-valuative"}[].
:::

:::theorem "thm:two-open" (parent := "grp:two-open") (lean := "AlgebraicGeometry.HasCompactification.of_two_open_cover")
*The two-open compactification theorem.*
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
