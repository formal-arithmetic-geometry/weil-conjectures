## What changed

Proved `ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero` without changing its
signature. Retained and checked the explicit augmentation, diagonal transition, quotient
transition, strict squares, functor laws, and uniformly bounded strict cone tower.

Added two proved helpers in separate modules:
`Sheaf.RingTheory.KoszulPowerHomologyProZero` proves positive homology vanishing by
contraction and Artin–Rees; `Sheaf.RingTheory.KoszulConeHomologyProZero` computes eventual
vanishing of the actual strict cone homology maps from the positive-homology hypothesis.
The item then applies the existing bounded derived tower theorem.

Repaired return 4ea080127: removed both duplicate private degree-one identities,
`ExteriorAlgebra.koszulBoundary_zero_formula` from the cone helper and
`ExteriorAlgebra.powerBoundary_zero` from the item. Both modules now use the existing
`ExteriorAlgebra.koszulBoundary_zero_quotient_formula` through proof-only
`import all Sheaf.RingTheory.KoszulProjectiveResolution`, matching the established
usage in `KoszulNormalizedProjectiveResolution`. No change to the existing theorem
or its visibility was necessary. Both affected modules compile after this repair.

Updated the three DAG proof records to match the Lean. No existing definition or statement
changed, so there are no consumer adaptations. The namespace-opening change is recorded in
`coord/changes/noetherian-koszul-namespace-openings.md`, as requested by preflight.

All three modules compile with the server tool, individually below 60 seconds. The two new
helper theorems have exactly the standard axiom dependencies `propext`, `Classical.choice`,
and `Quot.sound`. The item also depends on `sorryAx` through the existing bounded-derived-tower
theorem, as expected for a stage-3 proof from declared dependencies.

## Proved and sorry left

Closed the original one hole:
`ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero`
(node `lem-weil-pbc-noetherian-koszul-augmentation-pro-zero`).

Also proved both helpers retained from the previous attempt:
`ExteriorAlgebra.koszul_power_homology_pro_zero`
(node `new-q2-koszul-power-homology-pro-zero`) and
`ExteriorAlgebra.koszul_cone_homology_transition_pro_zero`
(node `new-q2-koszul-cone-homology-pro-zero`).

There are zero `sorry` declarations in this delivery, zero holes added, and zero outstanding
split-offs. The existing dependency
`DerivedCategory.tower_proZero_of_bounded_homology_proZero`
(node `lem-weil-pbc-bounded-derived-tower-pro-zero`) remains unchanged and is the next
unproved input; it is not an added hole.

## No longer needed

Removed the cone helper's proof import `Sheaf.RingTheory.KoszulGeneratorChainMap`: its only
use was in the deleted duplicate proof. The item retains that module because it still uses
`boundary_wedge` to verify the transition chain maps. The cone node no longer lists
`new-q2-koszul-generator-chain-map` among its proof dependencies. The two private duplicate
lemmas are removed entirely; no aliases or renamed copies replace them. The new proof-only
import reuses only the elementary boundary identity, without invoking or assuming the
regular-sequence projective-resolution theorem of node
`new-j3-koszul-projective-resolution`.

Removed the item's direct proof import `Mathlib.RingTheory.Filtration`; Artin–Rees is now
used in the proved positive-homology helper, which imports it. The tensor-complex bifunctor
`def-pc-tensor-complex-sheaves` is not used in the proof: the statement already fixes the
exterior Koszul model and every transition is constructed directly in that model. Its
statement dependency and existing public import stay as before. No existing library module
is claimed to leave the targets' import closure. All other mathematical inputs of the plan
are retained, directly or through the proved helpers.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated a degree-one boundary identity already available as a
private theorem. Reusing it via `import all` resolves the landing refusal without any
statement change.

The retained cone helper incorrectly quantified over an arbitrary derived tower without
requiring any connection to the Koszul augmentations. That statement is false: a constant
nonzero tower is a counterexample. Replaced the undelivered helper by a precise statement
about the specified augmentations, diagonal transitions, strict squares, and positive-homology
vanishing; it is now fully proved. The original item's statement is unchanged.

The retained report's second-reader section was inaccurate for this dispatched session and
has been removed. No second reader was requested or claimed. The finite-generation radical
containment lemma replaces the plan's explicit pigeonhole exponent in degree minus one;
only existence of a sufficiently large exponent is needed. The blueprint unit route is
preserved.

## New nodes

`new-q2-koszul-power-homology-pro-zero`, in
`lean/Sheaf/RingTheory/KoszulPowerHomologyProZero.lean`, records the proved contraction,
Artin–Rees, and diagonal-image argument. It has no residual proof obligation.

`new-q2-koszul-cone-homology-pro-zero`, in
`lean/Sheaf/RingTheory/KoszulConeHomologyProZero.lean`, records the proved strict cone
boundary argument. It explicitly assumes the positive-homology input and has no residual
proof obligation.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
