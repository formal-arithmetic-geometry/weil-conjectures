## What changed

Implemented `AlgebraicGeometry.topDegreeLeray_commutativeSquare` without changing its
statement. The data definitions now delegate to shared canonical image and comparison
constructions, preserving their exact mathematical objects and maps. The proof identifies the normalized tensor
adjunction with the adjunction of the pinned derived transpose, proves coefficient
naturality for the single direct-image comparison, and applies the top-cohomology
adjunction edge. Evaluation of the ordinary adjunction at the whole open gives
exactly `topDegreeSectionPullback`.

Added `Sheaf.AlgebraicGeometry.GlobalLerayUnitSquare`, proving the global ordinary
coefficient square from `derivedSquareUnit_localClasses`. Its restriction helper
uses the existing cohomology h-map restriction theorem, identifies its restricted
coefficient with `restrictedDirectImageMap` by adjunction injectivity, and pastes
the resulting cohomology square with the two classical edge comparisons. Its public
conclusion uses the native canonical comparison, matching the assigned theorem and
avoiding repeated conversion through the scheme-module aliases.
`globalLerayImage`, `globalLerayUnitMap`, and `globalLerayComparison` are real constructions
with the supplied derived-category family and universe fixed explicitly in their types.
They share the image and unit-map expressions across the global and top-degree
presentations, and are irreducible for importers. The proved API lemma
`globalLerayImage_isGE` exposes the nonnegative bound without expanding that data.
The existing top-degree image and comparison delegate to this data; their statement types are unchanged.

Added `Sheaf.AlgebraicGeometry.LerayEdgeRestrictedResolution` for the remaining
single-morphism compatibility between the chosen classical cocycle Leray edge
and `resolutionSectionClass` on an augmentation-preserving restricted resolution.
It has no square, derived pullback, derived adjunction, or cohomological bound.
All six changed/new modules passed their individual-file checks. The final
global-square implementation checked in 46.7 seconds with profiling enabled; the
clean top-degree module checked in 52.3 seconds. All four direct consumers passed against the changed dependencies:
`UnitAffineComparisonTransportCore` unchanged, and the three narrowly adapted
consumers listed below. No diagnostic options or probe files remain.
Profiling found repeated conversion between local wrapper instances and native module instances.
The module now selects native instances while defining the cached wrappers,
then uses the shared global abelian cache with native category and additive instances,
and explicitly checks their equality with the old abelian wrapper by `rfl`. The new proofs respect
transparency and use a whiskered natural transformation for single-image naturality.
The global proof clears the values of its chosen resolutions and restriction
comparisons, so later checks use abstract resolution data instead of repeatedly
unfolding the choice constructions. A proved generic section-evaluation helper
cancels the classical comparison and its inverse before the derived objects are
substituted, avoiding repeated conversions of their section group structures.

Imports needed only by proofs are private. The shared-data module is a public import
because it now supplies data used by existing definitions. Existing public imports,
public types, mathematical formulas, and source-library files are preserved.
The local instance selection changes definitionally equal implicit arguments; its
reason, old and new environments, and direct consumers are recorded in
`coord/changes/top-degree-native-module-instances.md`. Shared data and the consumer checks
are recorded in `coord/changes/top-degree-shared-leray-data.md`.


## Proved and sorry left

Original holes closed: `AlgebraicGeometry.topDegreeLeray_commutativeSquare`
(`lem-weil-pbc-top-degree-leray-square`), 1 of 1.

Also proved: `AlgebraicGeometry.globalLeray_unitSquare`
(`lem-weil-pbc-global-leray-unit-square`) and the private adjunction, coefficient
naturality, section-evaluation, wrapper-evaluation, and restriction helpers.

Holes added: 1, `AlgebraicGeometry.Scheme.Modules.lerayEdge_restrictedResolution`
(`lem-weil-pbc-leray-edge-restricted-resolution`). This is the only remaining textual
sorry in the delivery. Its source and complete proof in words are in the docstring
and node. This delivery is a decomposition: one original hole closes and one strictly
smaller compatibility hole is added, for net zero textual holes. The existing local
square and derived adjunction dependencies are used as stated, including any sorries
they transitively depend on.

## No longer needed

None. No existing import, module, declaration, node, or unit step is withdrawn.
The original local-square and cohomology-functoriality dependencies are now used in
the proved global assembly rather than directly in the final theorem. The original
node and the two new nodes record that dependency arrangement.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The current declarations already
supply the derived square transpose and arbitrary-square local class calculation.
The remaining interface gap is their passage to the separately chosen classical
Leray edge: the local square speaks in `resolutionSectionClass`, whereas the final
statement uses the cocycle edge selected from
`exists_lerayEdge_isIso_of_vanishing`. The new single-morphism compatibility isolates
that gap; the displayed arbitrary-square theorem is not restated under another name.

## Forced adaptations

`Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` (unclaimed): the original
`coherentEdge_typed_pasting` failed at `exact raw` (line 727). The raw theorem's
endpoints were the expanded Rf_*(G[0]) expressions, while the goal retained
`globalLerayImage f G` after unfolding `topDegreeDerivedImage`. The existing line
`delta topDegreeDerivedImage` now reads
`delta topDegreeDerivedImage globalLerayImage`. This expands the new alias in the
same place as the old alias. That version passed type checking but took 64 seconds,
above the 60-second limit. Immediately before the private proof section, local
instance priorities now select `SheafOfModules.instCategory`,
`SheafOfModules.instPreadditive` (3000), and `globalLerayModuleAbelian` (4000),
matching the dependency's native dictionaries. The exported edge/coefficient data declarations precede this selection and are
unchanged. All existing definition-body text, declaration type text, visibility and
imports remain unchanged; later private helpers and cached local instances store
definitionally equal native instance arguments. The
corrected consumer compile was accepted.

`Sheaf.AlgebraicGeometry.CurveAffineEdge` (unclaimed): the original failed at
`edge_delta_isIso`'s `change` (line 180), at the structural-unit map (line 246), at
the H1 finite-locally-free conversion (line 252), and at the coherent-edge theorem
application (line 255). Each error compared the expanded structural derived image
with `coherentEdgeK`, which now ends in `globalLerayImage`. Extend its existing
`attribute [local semireducible] topDegreeDerivedImage` with `globalLerayImage`.
No other source line changes; the adapted compile was accepted.

`Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` (no current claim
found): the original two local-instance proofs failed at `change` (lines 227 and
232), comparing `derivedStructureH1 f` with the homology of the opaque
`globalLerayImage f (SheafOfModules.unit ...)`. Add `globalLerayImage` to the two
existing `unfold coherentEdgeCohomology coherentEdgeK topDegreeDerivedImage` lines.
These are its only changed lines; all declaration types and data bodies are
preserved. The adapted compile was accepted.

## New nodes

`lem-weil-pbc-global-leray-unit-square` records the proved local-to-global assembly for
an arbitrary ordinary h-map and a local-class edge. It uses the stated local square,
cohomology restriction, and the new classical edge comparison. Its statement
dependencies cite the local-class data nodes; the top-degree parent supplies the
edge from the derived adjunction theorem.

`lem-weil-pbc-leray-edge-restricted-resolution` records the remaining compatibility
for one morphism and one restricted injective resolution. Its edge cases include
all natural degrees, zero coefficients, empty opens, and the whole open. Its proof
uses the existing restriction-on-resolution-cohomology theorem and the cocycle
characterization of the chosen Leray edge.

Change record: `coord/changes/top-degree-native-module-instances.md` (open).

Change record: `coord/changes/top-degree-shared-leray-data.md` (open).

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
