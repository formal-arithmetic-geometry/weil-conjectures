## What changed

Replaced the original `coefficient_tower_shriek_calculus` sorry by a compiling
assembly of the recorded shriek-level operations, section coordinates, geometric
composition, and actual transition compatibility. Its signature is unchanged.
Constructed finite direct-image coordinates from the normalized coefficient Hom
bijection. Proved reduction identity, composition and naturality, and proved
reduction-comparison invertibility from `reductionDirectImage_isIso`, including the
ell-power annihilation and finite cohomology-support hypotheses.

The three remaining independent arguments have named statements in three new
modules. Each has its source, full proof plan, own DAG node and exactly one sorry.
The existing interfaces were moved unchanged to `CoefficientTowerShriekInterfaces`
and publicly reexported, so these new modules have acyclic imports. See
`coord/changes/K6-coefficient-tower-shriek-interface-relocation.md`.
All five delivered modules compiled together after the elaboration adjustment:
the interface took 35.5 seconds, the three new statement modules 6.8--7.8 seconds,
and the assigned module 11.4 seconds.
The unchanged interface block was compared mechanically with the current source.
A later dry run exceeded 60 seconds on the interface. Profiling found cumulative
elaboration/type checking and instance search, not a single long proof. The interface
now uses the tested transparency settings and avoids generic small-site transport
for proposition-valued sheafification instances, restoring the inherited instance
priority at the module boundary. No definition body or signature changes.
The required dry run passed compilation and preflight at commit `1f9181018f`,
with review class CODEX. No delivery was pushed by that dry run.

## Proved and sorry left

Original holes closed: one, by declaration name:
`AlgebraicGeometry.ProEtale.SpTowerCalculus.coefficient_tower_shriek_calculus`.
This is a decomposition, not a complete proof of its transitive dependencies.

Holes added and left: three, each strictly a separate part of the argument:

- `AlgebraicGeometry.ProEtale.SpTowerCalculus.coordinates_realization`
  (`lem-sp-tower-section-coordinates`): ordinary section/evaluation and scalar
  coordinates only; no geometric operations or preservation assertion.
- `AlgebraicGeometry.ProEtale.SpTowerCalculus.geometric_calculus`
  (`lem-sp-tower-geometric-composition`): finite normalization, proper/open
  composition and etale sum-extension under preservation; no reduction law.
- `AlgebraicGeometry.ProEtale.SpTowerCalculus.reduction_transition_compatibility`
  (`lem-sp-tower-transition-compatibility`): the actual transition equality only;
  neither invertibility nor the formal reduction identity/composition/naturality.

There is no sorry in the assigned module or the relocated interface module.
The packet closes one old hole and adds three (net minus two); it is not reported
as net sorry progress. Proved helpers: `finite_coordinates_exists`,
`finite_direct_ring_map`, `reduction_identity_aux`, `reduction_composition_aux`,
`reduction_naturality_aux`, `ell_torsion`, and `reduction_comparison_isIso_aux`.

## No longer needed

No module or node is pruned from the overall mathematical argument. The old proof
dependencies support the three retained lemmas and remain in their node plans.
Their imports now belong to those lemma modules, rather than the final assembly.
The following old direct proof imports are absent from the assigned module:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.EtaleSumStalks`
- `Mathlib.Algebra.DirectSum.Module`
- `Mathlib.FieldTheory.IsAlgClosed.Basic`
- `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`
- `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`
- `Sheaf.Paper.VaryingRingGraphSummand`

The assigned module adds private imports of the three lemma modules,
`Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback` and
`WeilConjectures.Compactification.Over`. Its original public imports stay public;
the additional public interface import reexports all original declarations.

## Where the brief, the DAG or earlier work was wrong

The interrupted packet's report said that the old private helpers were retained
and unverified; that report was stale. The helpers have now been checked and the
composition proof corrected using naturality in the correct direction and the
explicit evaluation definition. The finite-coordinate proof uses the existing
constant-ring direct-image identity rather than unresolved universe inference.
Temporary provider interruptions caused no delivery; no push was previously made.
The first completed dry run failed during worktree checkout with a 600-second
subprocess timeout. Its retry ended with exit code 137 without diagnostics.
Neither command pushed a delivery. The next dry run reached preflight and found
missing leansearch records for the new nodes. A real leansearch query was run and
its results recorded; the preflight found no other static errors. Two axiom probes
timed out at 60 seconds; all five ordinary module compiles passed.

A first intermediate statement in the resumed sandbox merely repackaged the
remaining target and was discarded. The delivered statements are separate proper
subresults. Their edge cases were checked against the interfaces: equal coefficient
levels use the canonical unitor, successive quotients use the canonical associator,
the zero input has finite empty cohomology support, and empty schemes introduce
no nonemptiness assumption. Etale preservation is placed after the preservation
hypothesis; it is not asserted for an arbitrary unproved preservation instance.

The original proof's geometric and semilinear interfaces do not directly supply
the cross-presentation coordinate comparisons or the complete geometric package
in this module's coordinates. These are precisely the retained obligations. No
claim of equality of derived maps is inferred merely from finite evaluation.

## New nodes

`def-sp-coefficient-tower-shriek-interfaces` attaches the relocated, unchanged public
definitions to their new interface module; it adds no mathematical assertion or hole.

`lem-sp-tower-section-coordinates` records the ordinary section-coordinate and
normalized scalar-adjunction identification in its own module.

`lem-sp-tower-geometric-composition` records Local pairs steps 1--6 with the
preservation-dependent etale package and open normalization, independently of
coefficient-reduction compatibility.

`lem-sp-tower-transition-compatibility` records Levels step 7 as the actual
transition equality. The reduction comparison's invertibility and the three
formal reduction laws are already proved in the assigned module.

Change record: `coord/changes/K6-coefficient-tower-shriek-interface-relocation.md`.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
