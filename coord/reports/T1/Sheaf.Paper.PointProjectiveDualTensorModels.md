## What changed

Replaced the single unfinished proof of
`WeilConjectures.PointProjectiveDualTensorModels.point_projective_dual_tensor_models`
by an explicit assembly of all nine clauses. Existing signatures, aliases, public imports,
and the actual coefficient, generator, unit, tensor and Hom constructions are unchanged.

Added three proved supporting modules: bounded finite-projective scalar dual/tensor algebra,
the normalized rank-one comparison and finite-projective adjunction units, and bounded
finite-free-retract sheaf extension models. The main proof directly proves finite homology,
ordinary K-flatness, transport of bounds and splittings across the normalized tensor map,
transport of uniform Tor amplitude, and the canonical ordinary-to-derived Hom comparison.
The latter uses finite-retract exactness and the bounded exact-term Hom theorem on the
specified K-injective resolution, rather than choosing an unrelated derived isomorphism.

Separated the remaining source arguments into three results: normalized extension versus
total tensor, normalized extension versus ordinary dual, and completed perfect-point
constructibility with uniform finite-reduction Tor bounds. Each has a self-contained
statement, source, proof in words and a new DAG node. This is a decomposition.

## Proved and sorry left

Original holes closed syntactically: 1 of 1, in
`WeilConjectures.PointProjectiveDualTensorModels.point_projective_dual_tensor_models`.
Its assembled proof depends on the three holes listed below; this is not an axiom-free
proof of the original theorem. Holes added: 3. Net hole change: +2 before accounting for
other imported dependencies. The item module itself has zero remaining `sorry`.

Proved new public theorems, each with zero holes:

- `CochainComplex.bounded_finiteProjective_dual_tensor`
  (`lem-pod-bounded-finite-projective-dual-tensor`).
- `WeilConjectures.PointDerivedHom.point_finiteProjective_adjunction_units`
  (`lem-pod-point-finite-projective-adjunction-units`).
- `WeilConjectures.PointDerivedHom.point_finiteProjective_extension_models`
  (`lem-pod-point-finite-projective-extension-models`).

Every new remaining hole, each exactly a named public theorem with `:= by sorry`:

- `WeilConjectures.PointDerivedHom.point_extension_tensor_comparison`
  (`lem-pod-point-extension-tensor-comparison`): descend the balancing map and its inverse
  through both sheafifications, then assemble its natural degree comparisons into the
  signed total tensor. This is only the tensor comparison, for arbitrary complexes.
- `WeilConjectures.PointDerivedHom.point_finiteProjective_dual_comparison`
  (`lem-pod-point-finite-projective-dual-comparison`): descend the finite-dual-basis
  evaluation map on slices and assemble the reversed signed degrees. This is only the
  ordinary Hom comparison; the main proof supplies the canonical derived comparison.
- `WeilConjectures.PointPerfectExtensionConstructible.point_perfect_extension_constructible`
  (`lem-pod-point-perfect-extension-constructible`): identify the actual completed point
  coefficient with the adic presentation, compute its finite reductions, and carry the
  same bounded interval through tensor with every degree-zero module.

No private helper, definition or instance contains a hole. Empty finite powers, zero terms,
and reversed support intervals were checked in the algebra/retract arguments and in the
remaining proof plans. In the dual comparison, pure constant generators need only generate
locally after sheafification: no assertion that all sections of a constant sheaf are globally
constant is used.

## No longer needed

Removed direct private proof imports from the item:

- `Mathlib.Algebra.Module.Projective`.
- `Mathlib.LinearAlgebra.Dual.Lemmas`.
- `Mathlib.RingTheory.Finiteness.Defs`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`.
- `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.AdicPerfectModelCompleteReduction`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.

The item now uses the independent-universe bounded-flat criterion instead of
`lem-pc-bounded-above-flat-kflat-site`, the explicit finite-power/retract argument instead of
`lem-sfb-constant-finite-free-presentation-extension` for the unit and flatness clauses,
and bounded exact-term Hom instead of
`lem-weil-pbc-ringed-site-bounded-free-rhom-model` for the canonical derived-Hom clause.
The corresponding obsolete direct maintainer tool-use entries were removed, preserving
the order of the remaining entries.

The completion, DVR, finite quotient and derived-change-of-rings dependencies remain needed
in the proof plan of the new constructibility node. The finite-free-presentation result also
remains there. Their direct imports into the assembled theorem are unnecessary, but this
packet does not claim to prune those nodes or modules globally. No module is withdrawn;
no unit statement or proof step is bypassed, and no adopted-source declaration is removed.
Mathlib dual/projective/finiteness APIs remain used by the proved supporting modules.

## Where the brief, the DAG or earlier work was wrong

The existing generic scalar-dual and adic perfect-model results use different constant-module
presentations and, in several cases, identify site and coefficient universes. They do not
apply to the actual point models by definitional equality. The three new comparison nodes
state exactly the missing point-presentation compatibility; the proof does not silently
substitute a constant coefficient sheaf for the completed coefficient B.

No mathematical counterexample or target-statement change is proposed. The source route is
retained, with finite-projective algebra and adjunction units proved directly. All six new
nodes are below the same blueprint point-comparison statement and unit.

## New nodes

`lem-pod-bounded-finite-projective-dual-tensor`: Bounded finite-projective dual and tensor complexes. Lean module `Sheaf.Algebra.Homology.BoundedFiniteProjectiveDualTensor`.

`lem-pod-point-extension-tensor-comparison`: Normalized total tensor comparison for point extension. Lean module `Sheaf.Paper.PointExtensionTensorComparison`.

`lem-pod-point-finite-projective-adjunction-units`: Normalized finite-projective point adjunction units. Lean module `Sheaf.Paper.PointFiniteProjectiveAdjunctionUnits`.

`lem-pod-point-finite-projective-dual-comparison`: Normalized ordinary dual comparison for point extension. Lean module `Sheaf.Paper.PointFiniteProjectiveDualComparison`.

`lem-pod-point-finite-projective-extension-models`: Bounded finite-projective extension models. Lean module `Sheaf.Paper.PointFiniteProjectiveExtensionModels`.

`lem-pod-point-perfect-extension-constructible`: Constructibility and uniform Tor bounds for point perfect extensions. Lean module `Sheaf.Paper.PointPerfectExtensionConstructible`.

No definition or existing-statement change; no change record is required.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
