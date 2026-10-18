## What changed

Repaired the duplicate-theorem return at head `95ccdff38`. Removed the private
`AlgebraicGeometry.finrankH_unit_zero_eq_components`, whose statement duplicated
`finrankH_unit_eq_card_components` in
`Sheaf.AlgebraicGeometry.ProperSmoothGeometricComponentsLocallyConstant`.
The existing theorem is private. Instead of copying or exposing it, the item now
imports that module and uses its public
`AlgebraicGeometry.proper_smooth_geometric_components_locally_constant`.
That existing proof already uses the dimension theorem in question. Local
constancy gives finite range on the compact Noetherian base; the level sets are
clopen and therefore compact open and constructible. This replaces the entire
local degree-zero dimension argument with reuse of the existing public API.

Retained the earlier repair's complete proof of
`AlgebraicGeometry.projective_curve_betti_cardinalities`, with unchanged signature,
docstring and public imports. The new, fully proved module
`Sheaf.Paper.SmoothProperCurveNaturalCardinalities` computes the cardinalities for a
single possibly disconnected smooth proper curve. It decomposes into clopen
connected components, uses the existing connected-curve calculation, sums coherent
genera and assembles finite products of etale cohomology groups. The family proof
uses coherent rank constructibility in degree one for arithmetic genus, the
finite-range composition helper for prime powers, and the existing Ext/derived
comparison to establish the original cardinal-valued assertion. Serre duality
identifies arithmetic genus with the differential-form genus in the statement.

All added imports of the item are proof-only:

- `Sheaf.Paper.SmoothProperCurveNaturalCardinalities`;
- `Sheaf.AlgebraicGeometry.ProperSmoothGeometricComponentsLocallyConstant`;
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank`;
- `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`;
- `WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`.

Updated the item's node to record this exact route. Retained four new nodes from
the earlier delivery: the fully proved numerical lemma and three attachments to
existing source APIs. No existing statement, definition, visibility, exported
import or target changes; no other existing Lean module is adapted. The unit has
no realized statement or proof steps to bypass. Empty fibres give empty sums and
products; disconnected fibres use the sum of component genera; no base point is
chosen globally. The numerical lemma permits any coefficient integer nonzero in
the field, including one.

Validation: both delivered modules compile in import order with normal project
options, no errors or warnings, in 11.1 and 9.7 seconds respectively. Both pass
`tools/import_prune_check.py`, including the exact duplicate-theorem check that
returned the earlier delivery. The delivery dry run reports OK. Source checks
find no `sorry` tokens or lines over 100 characters, and every delivered node's
`proof_deps` is the union of its proof-step dependencies.

## Proved and sorry left

Closed the item's original one hole:
`AlgebraicGeometry.projective_curve_betti_cardinalities`
(node `lem-fin-projective-curve-betti-cardinalities`).

Added and fully proved:
`AlgebraicGeometry.smooth_proper_curve_natural_cardinalities`
(node `lem-fin-smooth-proper-curve-natural-cardinalities`).

Zero direct holes remain in either delivered Lean module. Zero holes added; zero
split-offs. The three source-API attachments add no Lean file or hole. Existing
dependencies can still contribute `sorryAx` transitively; this delivery closes the
local hole and does not claim all of curve cohomology is globally sorry-free.
The repair itself removes a redundant proved helper and introduces no hole.

## No longer needed

Removed the duplicate private helper `finrankH_unit_zero_eq_components`. The item
no longer directly imports `Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct`
or `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`; the existing
component-count module owns their use. Its node
`lem-weil-pbc-proper-reduced-algclosed-global-sections-product` remains necessary
transitively, rather than as a direct proof dependency of this item.

The previous report's claim that the proper-smooth component-local-constancy route
was pruned is withdrawn: that public theorem and its dependencies are now reused.
No whole-library pruning count is claimed.

Removed these direct proof imports from the original item:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`;
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
- `Sheaf.AlgebraicGeometry.SmoothCurvePointsDecomposition`;
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`;
- `Sheaf.Topology.RestrictInjectiveResolution`;
- `Sheaf.Topology.RingedSpaceModuleCohomology`;
- `WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective`;
- `Sheaf.AlgebraicGeometry.Coherent`;
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`;
- `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`;
- `WeilConjectures.AlgebraicGeometry.Curve.Estimate`;
- `WeilConjectures.ConstructibleSheaf.Defs`;
- `Sheaf.Paper.FiniteCoproductCohomologyAssembly`;
- `Sheaf.AlgebraicGeometry.ProjectiveFlatCoherentRanks`;
- `WeilConjectures.AlgebraicGeometry.Coherent`;
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`;
- `WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives`.

`Curve.Estimate` and `FiniteCoproductCohomologyAssembly` remain used below the new
numerical lemma. In particular, `thm-sc-proper-cohomology`,
`lem-weil-pbc-finite-coproduct-cohomology-assembly` and
`lemma-constructible-pullback-constant` remain necessary. The numerical proof builds
its clopen decomposition directly, so it does not use
`lem-sbc-smooth-curve-points-decomposition`. Coherent genus additivity uses the
existing source clopen cohomology formula rather than reconstructing injective
resolutions here. The source rank theorem works with the structure module's
existing quasicoherence and finite presentation instances, so the wrapper
`Sheaf.AlgebraicGeometry.ProjectiveFlatCoherentRanks` and explicit conversion via
`pqf-lem-coherent-ft-locnoeth` are unnecessary in this item. Primitive-root choice
is handled by the existing connected-curve theorem. Removed all eleven obsolete
top-level `tool_uses` entries from the item; the proof steps name the APIs used.

The earlier import-cycle repair is retained: there is no import of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve`. The unlanded
attachment `lem-fin-projective-curve-natural-cardinalities` is not delivered.
No existing node or module is deleted or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned delivery independently reproved an existing private dimension helper.
Its statement was identical, and the import-pruning gate correctly rejected it.
This repair removes the duplicate entirely and reuses the existing module through
its public component-count theorem. No attempt is made to rename the duplicate
or change its binders to evade the check.

An earlier returned proof imported `Finiteness.ProjectiveCurve`, closing a source
import cycle through general finiteness. The retained single-curve numerical lemma
avoids that import. The upstream-verbatim rule is respected: source-library files
are unchanged. No project or launcher script was edited or bypassed.

The retained source-cohomology attachments document APIs not individually attached
in the DAG before this work, with their actual finite-dimensional and flatness
hypotheses. No statement was weakened and no new statement is disputed. Previously
reported issues below Grothendieck spectral sequence nodes and the absent
`def-weil-pbc-ideal-module-product-stalk` are not introduced or modified here.

## New nodes

`lem-fin-smooth-proper-curve-natural-cardinalities` is the fully proved pointwise
numerical calculation in `Sheaf.Paper.SmoothProperCurveNaturalCardinalities`.
It has no family or constructibility conclusion and is strictly part of the
argument, not a restatement or moved hole.

`lem-fin-proper-coherent-finite-dimensional` attaches the existing
`Scheme.Modules.finiteDimensional_H_of_isProper` in source `DirectImage.AffineMorphism`.

`lem-fin-coherent-clopen-finrank` attaches the existing
`Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint` in source `Cohomology.EulerChar`.

`lem-fin-geometric-coherent-source-ranks` attaches the existing
`Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre` in source
`DirectImage.GeometricFibreRank`.

All four retained nodes include their sources, natural-language proofs, exact
Lean signatures and search records. No additional node is added for this repair.
No change record is needed: all existing public interfaces are unchanged.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
