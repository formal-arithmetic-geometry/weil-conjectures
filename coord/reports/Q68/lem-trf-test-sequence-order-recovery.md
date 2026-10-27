## Worker report

This delivery states `AlgebraicGeometry.HilbertSamuel.test_sequence_order_recovery` in
`Sheaf.AlgebraicGeometry.TestSequenceOrderRecovery`. Its proof is `sorry`; no theorem is
proved. Two definition modules provide the missing boundary order and common realized
finite test paths. Their data are explicit, with no `sorry`, choice of an unspecified
object, or extra geometric axiom.

Source reading: the publisher's complete BM paper was opened at
https://ems.press/content/serial-article-files/41043. Definitions 2.1--2.5, printed
pp.618--620, specify the smooth closed supports, ordered transverse smooth boundary,
controlled versus ordinary transforms, appended line zero section, and exceptional
intersection tests. Theorems 6.1--6.2, printed pp.631--633, recover the normalized point
and boundary orders on cosupport. Section 5, formula (5.4), defines the boundary order.
Theorem 6.1 explicitly discusses infinite order for the zero ideal. Definition 2.1 allows
smooth boundary hypersurfaces that are not globally irreducible. The node's given proof
supplies its extension to arbitrary scheme points and to all common finite prefixes.
The latest blueprint was searched through `tools/blueprint_refs.py`: its ancestor is
`lem-trf-local-term-locality`, and neither new definition has its own blueprint unit.
No statement correction or statement dispute is needed.

Hypotheses and conventions, clause by clause:

- The ambient smooth finite-type rational scheme is `S.Z`, with structure map `S.p`:
  `S.smooth` is `Smooth S.p`, and `[LocallyOfFiniteType S.p] [QuasiCompact S.p]`
  express finite type. `ULift.{u} ℚ` preserves the rational field while allowing schemes
  and their stalks in every universe `u`. It imposes no dimension or nonemptiness bound.
- The two smooth closed supports are `M.N` and `P.N`. The inclusions are `M.j`, `P.j`,
  their closed-immersion witnesses are `M.closed`, `P.closed`, and their smooth rational
  structure maps are `M.smooth`, `P.smooth`. A closed subscheme of the finite-type ambient
  is finite type, so finite type of the supports is not an extra input.
- The coherent ideals and positive marks are `M.ideal`, `P.ideal`, `M.marking`,
  `P.marking`, and the fields `M.coherent`, `P.coherent`, `M.positive`, `P.positive`.
  `Marked.coherent` uses the recorded quasi-coherent/finite-type predicate. On these
  smooth schemes over a field, local Noetherianness identifies it with coherence;
  the declaration's existing docstring explicitly records this identification (01XZ).
- The finite ordered boundary is the existing list `S.boundary`. `hboundary` uses the
  recorded `IsStrictNormalCrossingsBoundary` on the intersection of its ideal sheaves,
  whose vanishing set is their union. `hordered` identifies the given ordered members
  by their distinct local coordinate equations; this does not pick a different list
  from the existential components of the SNC predicate. Empty families are included.
- Transversality to both supports, meaning that the same labelled boundary equations
  restrict to distinct coordinate parameters there, is exactly `hM` and `hP` using
  `HasAdaptedNormalCrossingsCenter` for the bottom ideal. The condition is imposed
  everywhere on each support, since the bottom ideal has full support.
- `hdim` equates the Krull dimensions of the local rings of the two supports at points
  with the same ambient image. It expresses the stipulated same local support dimension;
  no equality of supports, ideals, marks, or coordinate systems is imposed.
- `hequivalent : RestrictedEquivalent M P` uses the existing depth-wise equivalence for
  all finite test words including open restrictions. It includes equality of cosupports
  and existence of all successors, rather than an arbitrary implication about supplied
  maps. Equality of cosupports is the geometric characterization of equality of sequence
  sets, as proved in step 1 of this node. No numerical-order equality is hidden in it.
- Point order is the existing `HilbertSamuel.order`, the supremum of maximal-ideal-power
  containments of the actual `stalkIdeal`; zero stalk ideals have infinite order.
  The existing `Marked.cosupport` is its order-at-least-mark locus in the ambient.

Operations and conclusions, clause by clause:

- `CommonTestSequence` records actual finite common prefixes, not an assumed abstract
  family of maps. Its `nil` constructor gives the empty prefix. `geometric` uses the
  existing `Step`, `Step.Admissible` for both current cosupports, and both `Step.Transforms`.
  `Step.geometry` uses the recorded global blowup, smooth center and adapted NC condition;
  the line case pulls back the ordered boundary and appends `lineZero`.
- `Step.Transforms` uses the actual scheme-theoretic strict support transform for a
  cosupport blowup. Its ideal equality is
  `M'.ideal * exceptional ^ M.marking = M.ideal.comap supportMap`, precisely controlled
  division by the exceptional marking-th power. Line products and exceptional-intersection
  blowups use cartesian support pullback and ordinary ideal pullback. Distinct boundary
  labels and their scheme-theoretic intersection are fixed by `Step.geometry`.
- The `restriction` constructor uses an actual open immersion `f` over the rational base,
  pulls back the ordered boundary, and uses both existing `MarkedPullback` relations.
  Arbitrarily many restrictions may occur at arbitrary intermediate stages.
- The theorem universally quantifies over the final ambient `T`, both transformed marked
  data `M' P'`, and `CommonTestSequence M P M' P'`. Thus it asserts both conclusions
  after every common finite prefix. Taking `nil` recovers the original-stage conclusions.
- At the final stage, `x : M'.N`, `y : P'.N`, and `M'.j x = P'.j y` specify the same
  ambient scheme point. The next two hypotheses put it in both ambient cosupports.
  They allow arbitrary scheme points, including nonclosed points. There is no conclusion
  at a point outside common cosupport.
- The first conjunct is
  `order M'.ideal x * P'.marking = order P'.ideal y * M'.marking` in `ℕ∞`.
  Since both marks are positive, this is exactly equality of their normalized extended
  rational orders, including infinity. It avoids truncated division in `ℕ∞` and the
  loss of infinity from coercing through `ENat.toNat`.
- The second conjunct quantifies over every current ordered boundary label
  `i : Fin T.boundary.length`, including newly appended components. It states the same
  cross-multiplied equality for `boundaryOrder` of the actual boundary ideal pulled back
  along each support inclusion. `boundaryOrder` is zero if that component misses the
  support point, and otherwise is the specified supremum of stalk ideal power containments.
  In particular a zero ideal at a point ON the component has infinite boundary order;
  a missing component has boundary order zero even for the zero ideal.

Dependency declarations reused:

| Node | Recorded module and declarations used |
| --- | --- |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact: LocallyOfFiniteType, QuasiCompact |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType: Scheme.Modules.IsQuasiCoherentFiniteType; public WeilConjectures.AlgebraicGeometry.Coherent: RingedSpace.IsCoherent |
| def-nagata-global-blowup | WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup, blowupMap |
| def-nagata-strict-transform | WeilConjectures.Compactification.StrictTransform: strictTransform, strictTransformMap, strictTransformToSource |
| def-trf-strict-normal-crossings-boundary | Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary: IsStrictNormalCrossingsBoundary |
| def-trf-marked-ideal-order | Sheaf.AlgebraicGeometry.MarkedIdealOrder: HilbertSamuel.stalkIdeal, order |
| def-trf-hilbert-samuel-presentation | Sheaf.AlgebraicGeometry.HilbertSamuelPresentation: Embedded, Marked, Marked.cosupport, Step, Step.Admissible, Step.Transforms, MarkedPullback |
| def-trf-restricted-marked-tests | Sheaf.AlgebraicGeometry.RestrictedMarkedTests: RestrictedEquivalentThrough, RestrictedEquivalent |
| def-per-adapted-normal-crossings-center | Sheaf.AlgebraicGeometry.AdaptedNormalCrossingsCenter: HasAdaptedNormalCrossingsCenter |
| def-sbc-ideal-sheaf-powers (new node prerequisite) | Mathlib.AlgebraicGeometry.IdealSheaf.Basic: IdealSheafData ideal multiplication and powers |
| def-weil-open-immersion (new node prerequisite) | Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion |

The added existing-node dependencies record the exact landed definitions used, rather than
private copies. Original dependencies are all retained. Stated proof dependencies are imported
without `public`: MarkedControlledBlowupCharts, PermissibleCoordinateChart, Regular,
RegularLocalRing.Defs, KrullDimension.Regular, FiniteTypeDimensionFormula, and
ClosedIrreducibleDimensionTrdeg. Mathlib's Jacobson result is already exposed by FiniteType.
The normal-slice, logarithmic differential, isotropic and anisotropic proof dependencies
currently have no recorded statement module and therefore cannot yet supply an import.

Edge cases checked before finalizing the statement:

- Empty ambient or either empty support: there is no paired common cosupport point.
- Empty boundary: `Fin 0` makes the boundary conclusion vacuous, while point order remains.
- Zero ideal: its point order and its boundary order on a component remain infinity;
  multiplication by a positive mark preserves infinity.
- Unit ideal: the positive marking makes its cosupport empty. No order is recovered there.
- Marks equal to one or unequal positive marks: cross-multiplication expresses exact
  rational normalization (e.g. 3/2 = 6/4), never rounded integer division.
- Zero-dimensional support: the statement allows it; on cosupport its ideal is zero.
- Nonclosed points: all binders are arbitrary scheme points, and `hdim` uses stalk rings.
- Disconnected supports, distinct supports, and varying dimensions: none is identified or
  required equidimensional; dimensions are compared only at the same ambient point.
- Missing boundary at the point, even with zero ideal: explicit zero branch is essential.
- Arbitrarily long prefixes and intervening open restrictions: the inductive path is finite
  with no predetermined length. Its empty constructor retains the initial assertion.

Searches made before defining anything:

1. `msearch.py ... leanfinder` queried test-equivalent marked ideals recovering normalized
   point and exceptional orders; eight unrelated ring-preordering, composition-boundary,
   and homology-embedding results, no matching theorem.
2. `msearch.py ... loogle 'Ideal, ENat, IsLocalRing.maximalIdeal'` returned DVR and length /
   Krull-dimension lemmas, none about marked-test equivalence or general boundary orders.
3. `msearch.py ... grep 'boundaryOrder|TestSequence|MarkedIdeal|test_equiv'` returned zero hits.
4. `msearch.py ... leansearch` queried boundary ideal order and finite common marked tests;
   the hits concerned fractional ideals, Ring.ord of elements, and Weierstrass series.
5. Targeted LeanSearch, LeanFinder and Mathlib grep for the two new notions are recorded
   verbatim in each new node's `mathlib_searches` (the raw outputs are preserved there).
6. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and `dag/lean_names_upstream.json`,
   including an item-id search in WeilConjectures, found no exact recovery theorem or names
   `boundaryOrder`, `CommonTestSequence`, or `test_sequence_order_recovery`. Concept searches
   found and reused MarkedIdealOrder, HilbertSamuelPresentation and RestrictedMarkedTests.
7. DAG searches and `blueprint_refs.py search 'test sequence'` / `'boundary order'` found
   no existing definition of either new notion. `MarkedIdealData.History` is different:
   it only records controlled admissible blowups with birth data, and excludes the other
   three operations required here. It was read but not copied or redefined.

## New nodes

`def-trf-marked-boundary-order` defines the boundary order by the prescribed supremum in
`Sheaf.AlgebraicGeometry.MarkedBoundaryOrder`, with the explicit zero-away-from-boundary
convention. Source: BM (5.4), Theorem 6.2, pp.629--633. It reuses the existing stalk-ideal
construction and ideal powers. The recorded searches found point order, element orders,
DVR exponents and fractional-ideal counts, none of which is this general stalk ideal
boundary order. The node has no postponed theorem.

`def-trf-common-marked-test-sequence` defines only a common finite path through the existing
marked tests in `Sheaf.AlgebraicGeometry.CommonMarkedTestSequence`, with a constructor for
open restriction. Source: BM Definitions 2.2--2.5 and the recovery node's explicit local-test
convention. Existing `RestrictedEquivalent` describes agreement at every finite depth, not
an actual common path with specified endpoints. Existing `History` covers only controlled
blowups. The new relation reuses every step and transform predicate instead of redefining
its operations. The searches are recorded in the node and no theorem is postponed.

## Second reading by Q68

Worker rereading of the node and all three modules, not a claim of an independent reviewer;
the assigned maintainer supplies the independent reading of the delivery. The rereading
matched the smooth rational finite-type ambient and supports to Embedded/Marked and the
finite-type instances; positivity/coherence to Marked fields; ordered SNC and transversality
to hboundary/hordered/hM/hP; local dimensions to hdim; test equivalence to RestrictedEquivalent;
the four operations to geometric/restriction; controlled versus ordinary ideal transforms
to Step.Transforms; arbitrary paired common cosupport points to x/y and their hypotheses;
and the two displayed equalities to the point-order conjunct and the universally labelled
boundary-order conjunct. The final universal path quantifier and nil constructor preserve
both the initial assertion and every common-prefix assertion. No source or node statement
was changed. The two elaboration fixes were adding classical decidability for the explicit
boundary-membership conditional and renaming the reserved binder `prefix` to `prior`.
