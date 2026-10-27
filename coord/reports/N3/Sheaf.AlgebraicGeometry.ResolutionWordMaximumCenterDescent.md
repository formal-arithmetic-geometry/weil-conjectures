## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_maximum_center_descent`
with a complete Lean assembly from a strictly smaller local comparison theorem.
The existing theorem signature and `ResolutionWordChart.finalMap` definition are unchanged.
No existing module besides the assigned item was edited; all existing public imports remain.

The proof constructs an attained positive greatest value from the finite image, constructs
its closed equality locus, and proves nonemptiness of its reduced induced subscheme.
It proves the final chart map etale and transports the chart's specified point using its
last-index equality. Scheme-point lifting for the cartesian square then gives a local
smooth center over every point of the global center. Flat-local regularity descent proves
the global regularity, including its local Noetherianity.

For density, Mathlib's component-generic stalk field lemma replaces the Serre-criterion
argument, and `genericPoints.closure` supplies density. For coherence, the adopted source's
`Scheme.Modules.isQuasicoherent_toModules` and `isFinitePresentation_toModules`, followed by
`isCoherent_iff_isQuasicoherent_and_isFiniteType`, handle both ideals directly.
The import-direction check for `Modules.HilbertPolynomial` returned yes.

Both delivered modules compile cleanly through `lcompile.py --all`: local models 13.4 s,
assigned module 18.5 s. The final delivery tool performs the axiom and packet checks.

## Proved and sorry left

Original item: 1 hole. Closed its body at
`AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_maximum_center_descent`.
No `sorry` remains in the assigned module.

Added 1 hole:
`AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_local_maximum_models`,
node `lem-trf-resolution-word-local-maximum-models`, in the new module
`Sheaf.AlgebraicGeometry.ResolutionWordLocalMaximumModels`.
Its whole proof is `by sorry` and its docstring contains the source and complete
natural-language argument from the parent's steps 3--4.

This is a decomposition, not a net hole closure: 1 original hole closed, 1 smaller hole
added, net 0. The remaining theorem assumes a supplied positive greatest value and its
closed equality locus and asserts only their local marked-history models. It asserts
neither existence of that value/locus nor global regularity, nonemptiness, component
avoidance, empty interior or coherence. Those conclusions are proved in the assigned
module, including the nontrivial descent from the local models.

## No longer needed

Removed private imports from the assigned module:

- `Mathlib.RingTheory.Noetherian.Basic`
- `Mathlib.RingTheory.Localization.Submodule`
- `Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile`
- `Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent`
- `WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `WeilConjectures.RingTheory.SerreCriterionReduced`

The regular-scheme public interface already exposes `IsRegular.of_smooth`, so its duplicate
private import is unnecessary. The profile, local-presentation, numerical-engine,
reduced-pullback and smooth-reduced inputs of old steps 3--4 remain dependencies of the new
local comparison node; their mathematics is not withdrawn. Existing public imports were
retained for compatibility.

`lem-weil-pbc-serre-criterion-reduced` is no longer needed in this argument: the generic
stalks are fields directly. `lem-weil-pbc-noetherian-submodule-finite` is replaced by the
already proved finite-presentation API for ideals. `lem-weil-pbc-localization-noetherian`
is no longer invoked separately: the scheme local-Noetherian/stalk instances supply the
Noetherian stalks. No modules or declarations are withdrawn, and no claim is made that
these source modules are unused by other target branches.

## Where the brief, the DAG or earlier work was wrong

The planned Serre R0 detour and explicit finite-generation reconstruction are unnecessary
with the existing library API. No mathematical statement or definition was corrected.
ILO VIII 2.3.11/2.3.13 (PDF pages 99--100, printed pages 93--94) points to the
Bierstone--Milman--Temkin algorithm rather than spelling out normalized-word comparison;
the new node therefore retains the parent's `proof_origin` as agent assembly.
The parent node's route and the unit/chapter route are preserved.

Edge cases reviewed: an empty or already regular stage contradicts the nonregularity
hypothesis once local Noetherianity is established; positivity excludes all regular points
from the maximum locus. The generic-point argument allows reducible and mixed-dimensional
schemes and does not require finitely many components. Final-index transport also covers
charts of length zero. The local-model lemma needs no nonregularity hypothesis because it
is supplied an attained positive maximum, and is vacuous when the closed locus is empty.

## New nodes

`lem-trf-resolution-word-local-maximum-models`, module
`Sheaf.AlgebraicGeometry.ResolutionWordLocalMaximumModels`, isolates exactly the parent
proof's local maximum comparison and reduced scheme-structure identification (steps 3--4).
It retains the same fixed engine, simultaneous assignment, admissible history, ambient
hypotheses and reducedness, and additionally receives the already constructed maximum and
its equality locus. The new statement is strictly a part of the original argument, with
no global descent/density/coherence conclusions. LeanSearch, LeanFinder and Mathlib grep
found no matching theorem; the imported-blueprint search for "maximum center" found no
blueprint nodes. No change record is needed: no existing statement, definition, attribute
or public import was changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
