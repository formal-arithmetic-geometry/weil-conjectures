## What changed

Prove `WeilConjectures.constructibleTruncations_exists` in
`Sheaf.Paper.ConstructibleTruncations`, preserving every public signature,
definition, and public import. Reuse the existing independently proved rational
and common-stage standard t-structures. Prove standard-class preservation by
finite scalar extension through the ordinary/completed comparison and exact
homology. Stage inclusions preserve their existential classes directly.

For scheme automorphisms use the published `isomorphismFieldTransport`: exact
module inverse image preserves homology vanishing and its integral comparison
transports this to completed pullback. Rational representative formulas and the
common-stage inclusion comparison prove t-exactness. Subsingleton equality of
residue-field invertibility structures reconciles the theorem's existential
families. The generic comparison lemma gives existence and uniqueness for both
truncations, and explicit functor associators, whiskering and the shift comparison
give the cohomology comparison.

Remove the unused private proof imports and update the proposition's proof route.
Attach the existing two independent t-structure existence proofs to the new node
`lem-pod-intrinsic-standard-tstructures`; no new Lean declaration is introduced.
The unit record has no realized statement/step requiring the abandoned lower route.

## Proved and sorry left

Closed: `WeilConjectures.constructibleTruncations_exists`
(node `prop-constructible-truncations`), 1 of 1 original holes.
Added: zero holes. Split off: zero holes. Remaining in the item: zero holes.
The imported declarations retain their existing independent proof obligations;
this delivery adds none. This is a proof from the library's named declarations,
not a claim that the transitive axiom closure has no pre-existing `sorryAx`.

## No longer needed

Removed private imports:

- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.Paper.SfDerivedComplete`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.IntegralTStructure`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.LocalizedTStructure`
- `Sheaf.Paper.ConstructibleStandardTStructure`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`
- `Sheaf.Paper.SfScalarExtensionComposition`
- `Sheaf.Paper.PbcScalarExtension`
- `Sheaf.CategoryTheory.StageSystemFunctorDescent`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Paper.PbcRationalTransport`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`
- `Sheaf.Paper.PbcDescentFunctors`

The direct planned dependencies no longer needed by this proof are:
`def-weil-derived-cohomology-sheaves`, `def-weil-finite-subextension-directed-set`,
`lem-a1-texact-coefficient-stage-descent`,
`lem-fin-finite-type-fibre-dimension-bound`,
`lem-pod-completed-scalar-extension-texact`,
`lem-pod-directed-pair-bounded-tstructure`,
`lem-pod-isomorphism-pullback-texact-coefficients`,
`lem-weil-linear-scalar-localization-triangulated`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-integral-stratified-perfect-characterization`,
`lem-weil-scalar-extension-exact-triangulated`,
`prop-weil-localized-tstructure`, `prop-weil-pbc-integral-tstructure`,
`prop-weil-pbc-scalar-extension`.
The existing intrinsic t-structure and exact field-transport implementations
supply the portions of this infrastructure actually needed. Some remain needed
transitively by those implementations and other consumers: none is withdrawn.
The generic exact-functor and homology tools remain direct dependencies because
the private helpers use their exact derived homology API. Obsolete top-level
`tool_uses` entries are removed in their original order:

- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `prop-weil-pbc-integral-tstructure`
- `prop-weil-localized-tstructure`
- `lem-fin-finite-type-fibre-dimension-bound`
- `lem-weil-finite-free-completed-scalar-comparison`
- `lem-weil-integral-scalar-extension-constructible`
- `lem-weil-scalar-extension-exact-triangulated`
- `lem-weil-proetale-isomorphism-inverse-image`
- `lem-weil-proetale-countable-products-exact`
- `lem-weil-derived-limit-existence`
- `lem-pur-integral-operations-preserve-constructible`
- `lem-pur-integral-operations-scalar-extension`
- `lem-pur-isomorphism-inverse-image-tensor-hom`
- `lem-weil-isomorphism-derived-pullback`
- `prop-weil-pbc-rational-transport`
- `lem-sbc-coherent-pair-functor-descent`
- `prop-weil-pbc-descent-functors`
- `lem-pur-semilinear-scalar-localization`
- `prop-weil-pbc-scalar-extension`
- `lem-a1-texact-coefficient-stage-descent`
- `lem-weil-linear-scalar-localization-triangulated`

No library module or declaration is deleted. Actual target-closure pruning is
for the maintainer's ledger to measure; no transitive pruning is claimed here.

## Where the brief, the DAG or earlier work was wrong

The old proof imports include legacy-category t-structures, while the assigned
statement uses intrinsic sf categories. `SfConstructibleHeart` now independently
proves exactly the required intrinsic existence and boundedness assertions; the
long legacy comparison route is unnecessary.

The general heart node has a statement dependency on this proposition although
these two t-structure proofs no longer use it. Citing that whole node would create
a DAG cycle. The new attachment isolates the already proved existence clauses
without changing the heart node or using its abelianity conclusions.

The newest blueprint uses an ambient condensed-coefficient constructible
subcategory, while the assigned Lean statement is the previously reviewed raw
rational/common-stage interface. This delivery preserves that entire interface
and follows the standard-class, exact scalar-extension and exact inverse-image
argument; it does not silently replace the assigned categories. A future global
statement migration remains distinct from this proof delivery.

A whole-graph DFS also encounters a pre-existing remote dependency cycle at
`lem-pc-ring-hom-extension-differential`; this delivery changes none of those
nodes. The separate reachability check establishes no path back to this item.

The source exists in lean despite the older quarantine/rework row; the actual
current source is preserved, and no quarantined path is withdrawn.

## New nodes

`lem-pod-intrinsic-standard-tstructures` attaches the existing
`WeilConjectures.sfRationalStandardTStructure_existsUnique` and
`WeilConjectures.sfCommonStageStandardTStructure_existsUnique` in
`Sheaf.Paper.SfConstructibleHeart`. It asserts only their independent existence,
uniqueness and boundedness clauses, strictly less than the proposition with all
scalar and automorphism comparison clauses. Its two proof steps follow the
existing Lean proofs. Searches found ambient Mathlib t-structure infrastructure
and this exact project implementation. No new Lean module, statement, `sorry`,
axiom, arbitrary witness or interface change is introduced. No change record is
needed: all public statements and definitions are unchanged. Edge cases checked:
the empty scheme, zero objects, identity field extensions, negative shifts, and
automorphisms without base-field linearity. Existence/uniqueness follows from
the same prescribed class functions in each case; no separatedness or reflection
of bounds by a stage transition is assumed.

Validation: the complete item compiled through the required `lcompile.py` with
exit code 0 in 13.2 seconds and no warnings or errors. Node JSON parses,
proof-dependency unions agree, and the combined DAG has no cycle back to the item
(12,138 reachable nodes checked). Every Lean line has at most 100 characters;
all three public definitions and both public imports are unchanged.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
