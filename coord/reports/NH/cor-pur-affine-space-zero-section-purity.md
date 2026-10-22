## Worker report

`Sheaf.Paper.AffineSpaceThomMap` constructs the supported coordinate product and
its exceptional adjunct. `Sheaf.Paper.AffineSpaceZeroSectionPurity` states purity
with the inverse normalized by the recorded ordered affine-space comparison.
Every definition has actual data; every postponed proof is a named theorem.
No node statement is corrected and no hypothesis is added.

Clause-by-clause rendering:

- The finite datum is `P : PurityFiniteSetting`. The natural number `n` indexes
  the positive level `n+1` through `setting P n`. This ranges over every allowed
  level, with no ramification-divisibility restriction. The original level of P
  is replaced by the quantified positive level; its field and coefficient extension remain
  exactly those of P.
- `B : Scheme.{u}`, `aB : B ⟶ Spec (.of P.field.k)` and the instances
  `LocallyOfFiniteType aB`, `QuasiCompact aB`, `IsSeparated aB` express separated
  finite type over k. The recorded comparison takes the explicit structure map.
- `c : ℕ` includes dimension zero. `iteratedAffineLine B c` is the recorded
  ordered affine-space model, built from relative affine lines, with literal
  `X₀=B`. `iteratedAffineLineProj` is its projection and `zero` sets every
  coordinate to zero. `divisor` is the actual coordinate zero subscheme.
- `ordinaryBoundary` uses the unique normalized simultaneous family from
  `Etale.cartier_kummer_map`, evaluated at an explicit annihilating exponent.
  `realizeBoundary` uses closed site exchange, the degree-zero exact comparison,
  and the actual Ext arrow. The family's `CartierKummerRealization` quantifies
  over every annihilating exponent with the projection-normalized comparison;
  it supplies exponent independence, including at ramified levels.
- `target` is the ordered tensor power of the recorded compared shifted finite
  Tate line. Its c factors are precisely A(c)[2c], with literal coefficient unit
  at c=0. It reuses `AffineSpacePurity.shiftedLine` from the comparison module.
- `cupZero` is `supportedCup` in degree zero after cancelling zero-shift unitors:
  it invokes the published `supportedCup` at degrees (0,0), composing with
  the canonical zero-shift unitors. The same coefficient multiplication and
  tensor of arrows are used. `product` iterates this operation on the actual coordinate support
  intersections, starting with the constant-unit identity.
- `supportIso` is selected from an existence-and-uniqueness assertion over the
  affine space: it is fixed by its immersion into X, not an arbitrary chosen
  isomorphism. `supportedClass` is the product transported to the zero section.
- `thom` is the published exceptional Hom-bijection applied to this exact
  supportedClass, after the canonical proper/closed direct-image comparison.
  Thus the assertion that 1 maps to the coordinate product is in its definition.
- `zeroSection_purity` asserts invertibility of thom and both inverse equations
  for `normalization`. The latter applies Rz! to the actual ordered `gamma`,
  followed by `collapse`: the inverse conjugate of compact-support composition,
  equality transport along pz=id, and the inverse normalized identity unit.
  The inverse equation is exactly the adjoint formulation of integration of the
  zero-section class to 1, by the composite-counit formula.
- `zeroSection_purity_untwisted` states the equivalent isomorphism in the derived
  category, using the recorded negative finite Tate twist and shift [-2c].
- `zeroSection_purity_baseChange` covers any g between the two separated
  finite-type bases, with the equation `g ≫ aB = aB'`. `zeroSquare` is the
  coordinate Cartesian square. `classBaseChange` is the actual closed exchange,
  exact derived inverse image, and canonical tensor/Tate pullback comparison.
  Equality of the supported arrows is equivalently the exceptional base-change
  square for their adjuncts. No flatness or smoothness of g is assumed.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `constantEtale`, `constant`, `Coefficient`.
- Mathlib affine space and morphism modules: `AlgebraicGeometry.AffineSpace`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: specified finite Tate
  objects reexported by this module; no replacement coefficient system.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: exceptional
  functor interface, realized here by the published `rightDerivedUpperShriek`.
- `Sheaf.AlgebraicGeometry.CartierKummerMap`: `Etale.cartier_kummer_map` and its
  uniquely normalized ordinary family and exponent-independent realization.
- `Sheaf.Paper.PurityAffineLineOrientation`: `affineLine_orientation`; its
  original divisibility domain is preserved, not imposed on the present theorem.
- `Sheaf.Paper.PurityAffineLineDatum`: the named rank-one normalization domain.
- `Sheaf.Paper.SupportedCup`: `cupSingle`, `cupTensorObject`,
  `supportedCup`, `cupIntersection`, `cupSingle` and `cupConstantIso`.
- `Sheaf.Paper.SupportedCupFunctoriality`: `functorialCupSupportMap`,
  `functorialCupExchange`, `functorialCupTwist`, `functorialCupSingle`,
  `functorialCupSource`. Their owner `def-pur-supported-class-operations` is
  cited in stmt_deps for these existing operations.
- `Sheaf.Paper.AffineSpacePurityComparison`:
  `AffineSpacePurity.affineSpacePurityComparison`, `shiftedLine`, `orderedSource`,
  `compositionInverse`, `actionPullbackIso` and its canonical tensor comparisons.
- `Sheaf.Paper.AffineLinePurityComparison`: the all-level integration-transposed
  affine-line factors used by that ordered comparison.
- `SpecifiedExceptionalClassHom`, `CanonicalOriginCompactSupportComposition`
  and the published six-functor modules provide the actual Hom equivalence,
  closed proper comparison, identity/composition normalization and inverse image.
  The node's other proof dependencies are imported as the stage-3 proof plan.

Edge cases: c=0 has no coordinate divisor and uses the empty constant unit;
its exceptional normalization is the canonical identity-adjunction one. c=1
is the rank-one Cartier orientation. Empty, disconnected, and nonreduced bases
are allowed: coordinates remain nonzerodivisors over arbitrary rings. Ell=2
has no exceptional sign because coordinate degrees are even. Every positive
coefficient level is included, in particular ramification index 2 at level 1.
Identity, arbitrary nonflat, and empty-base changes are retained.

Searches made before implementation:

- Launcher msearch LeanFinder: “affine space zero section purity supported Kummer
  cup product Thom isomorphism”; eight unrelated ring/affine-chart results,
  no purity statement.
- Launcher msearch Loogle: “AlgebraicGeometry.AffineSpace.zeroSection, IsIso”;
  no match (unknown proposed zeroSection identifier).
- Launcher msearch Mathlib grep: “zeroSection|Thom|thom” in AlgebraicGeometry;
  unrelated zero sections and author names, no supported Kummer purity.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for zero-section purity, Thom,
  Kummer and supported cup; the recorded ingredients exist, but no declaration
  with this statement, canonical product, ordered inverse and base-change clauses.
- grep for the exact node id in `lean/WeilConjectures`: no existing declaration.

Additional comparison of existing project declarations: upstream
`Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord` is an ordinary-etale
result with an abstract normalized `HasKummerClass` instance; it does not state
the all-level specified pro-etale comparison or the inverse/integration and
base-change assertions here. `PurityFiniteSetting.frameClass` takes an etale
frame and its smooth-relative-dimension hypotheses and returns its signed frame
class; it is not the coordinate realization in the ordered-gamma target. The
localized-top-Chern `vectorBundleThomClass` is another construction and is not
used to replace the source's supported-Kummer proof route. The present product
uses the recorded supportedCup directly.

## Statement self-audit by NH

The dispatcher explicitly requires this worker to deliver without starting other
agents; the maintainer performs the independent review. This section records a
separate self-audit, not a claim of an independent worker's reading. I checked
finite-level indexing, the exact coefficient categories, the empty product,
all source and target functors, and the order of the inverse compositor against
the node's eight proof steps. The supported-arrow base-change equality is the
adjoint form of the stated exceptional compatibility. No source statement is
weakened and no new mathematical assumption is made.

In this separate pass I also read the new coordinate-boundary node against its
module: n+1 is the positive coefficient level, n+2 is merely a permitted killing
exponent, and the ordinary arrow, closed exchange inverse, and exact single
comparison are the arrows in proof Steps 1--3. The empty coordinate family and
zero-section identity are retained. The partial-support equalities introduced
during elaboration are exactly the `supportData` defining equations; they do
not replace an intersection by another support. The generic zero-degree helper
now calls the published `supportedCup` directly, rather than reassembling it.

## New nodes

`def-pur-affine-space-coordinate-boundaries` supplies the previously missing actual
coordinate boundary arrow in the compared shifted-line coordinates of ordered
gamma. Its source is the ordinary normalized Cartier family, reused rather than
redefined; its realization is the canonical closed exchange and exact comparison.
Source: the item's proof Steps 1--3. Searches in LeanSearch, LeanFinder, Loogle,
Mathlib, the project and DAG found the generic family and the rank-one Gysin
section, but no recorded construction of this precise coordinate derived arrow.
The node also names the positive-level reindexing and canonical coordinate geometry
used by it. Its level starts at n+1 and uses the exact same finite rings and units.
This module has real map data; coordinate-Cartier and closed-zero-section facts
are named statements with their polynomial-chart proofs in their docstrings.

The literal partial-support object is named `classSource`. Its `nil`, `cons`
and unfolding equalities, and `target_succ`, merely expose the defining
intersections and tensor powers. Their equality transports keep Lean from
repeatedly expanding scheme pullbacks inside a dependent recursion. They add
no choice, no hypothesis, and no new mathematical assertion to the node.

`def-pur-affine-space-thom-map` names the missing canonical supported coordinate
class and its closed exceptional adjunct in the compared shifted-line target.
Its module is `Sheaf.Paper.AffineSpaceThomMap`; its primary declaration is `thom`.
The assertions about the inverse are in the corollary module. The helper reuses
supportedCup itself, the existing Cartier family, closed proper direct image,
and the exceptional Hom equivalence; it selects no unspecified isomorphism.
Source: proof Steps 1, 3 and 5. The new-node searches are recorded verbatim in
its mathlib_searches. The existing generic frameBoundaryProduct has a different
finite-Tate target; the existing vector-bundle class is constructed by localized
top Chern. Neither supplies this canonical exceptional adjunct in the target of
the ordered comparison. The new node introduces no alternate Kummer or cup API.

The coefficient-unit pullback uses the already published frameConstantPullback
with the exact derived degree-zero comparison `pullbackSingle`. This is the
canonical constant pullback, computed on sheaves, and avoids expanding the
monoidal-derived unit comparison. At c=0 the equality `zero_zero` is transported
by the published `rightDerivedUpperShriekCongr`; no replacement right adjoint is
chosen. All equality transports are explicit and keep the identity case.

`unit_single_eq` exposes precisely the existing cached degree-zero embedding;
the unit pullback uses equality transports at both endpoints. This equality is
not a new identification of coefficients or a choice of a derived equivalence.
Its complete proof is to unfold the recorded embedding and its shared canonical
localization instance, as documented next to the postponed statement.

The constant-pullback comparison to the ordered source is first constructed with
its literal computed endpoints as `targetSourceRaw`. The named left and right
equalities expose exactly the tensor target and the recorded ordered source.
`targetSourceIso` transports this same comparison along those defining equalities.
This follows the published comparison module's raw-endpoint interface and keeps
the degree-zero case as the literal identity. The ordinary witness for gamma uses
the exact single-functor comparison, followed by the inverse `unit_single_eq`
transport; no extra antecedent or origin assumption is supplied by the user.

The inverse candidate is likewise computed as `normalizationRaw`, with the
actual Rz!(gamma) map and published collapse in positive dimensions, and the
canonical identity-adjunction map in dimension zero. Named defining equalities
expose its endpoints for `normalization`. These transports retain the actual
maps, avoiding repeated unfolding of the exceptional functor in a dependent
case expression. They do not assert purity or choose an inverse of thom.

For the dimension-zero branch both endpoints of the identity exceptional
comparison are specified as B. Its compactification is the proper identity
compactification transported along `zero_zero`; this records the same geometry
without relying on instance search across the literal zero-stage tower.

Validation: scompile.py compiled every delivered file separately against the live
published library. The coordinate-boundary module passed (38.2 s), the Thom-map
module passed (49.9 s), and the complete corollary module passed (30.7 s), without
warnings other than permitted postponed-proof warnings. The sandbox checks also
passed. All temporary probes were removed from the delivery.

## Returned delivery repair (2026-10-22)

H2/H13, independent review of immutable head `0fa11caf2d20`: replaced
`lem-pur-supported-cup-functoriality` with the already-landed definition node
`def-pur-supported-class-operations` in the statement dependencies of both
`cor-pur-affine-space-zero-section-purity` and
`def-pur-affine-space-thom-map`. The latter node's statement citation now names
the definition node as well.

I read the landed definition node's existing:true record and the signatures and
docstrings of `functorialCupSupportMap`, `functorialCupExchange`,
`functorialCupSingle`, `functorialCupSource`, and `functorialCupTwist` in
`Sheaf.Paper.SupportedCupFunctoriality`. They supply exactly the operations
used by the retained modules. The conclusion of `supportedCupFunctoriality`
is not used to state either node. This repairs the ownership citations without
changing any mathematical statement or any Lean source. The retained packet
was first dry-run against current main successfully; its concrete changes from
the returned packet are the two dependency lists, the Thom-map citation, and
this report. The prescribed delivery wrapper rebuilds it on the current branch.

Repair validation: scompile.py returned exit code 0 for all three retained
modules separately, including both sandbox and library checks, with no errors
or disallowed warnings. Both repaired dependency lists cite the definition
node exactly once, and the Thom-map statement cites that same owner.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
