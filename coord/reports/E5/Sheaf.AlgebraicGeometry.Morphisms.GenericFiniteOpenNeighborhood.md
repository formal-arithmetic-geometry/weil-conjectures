## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers`
in `Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood`, preserving its complete
signature and all public imports. Eight proved private helpers realize the six-step Stacks 02NW
argument: genericity of fibre points, algebraic localization on spectra, transport through affine
isomorphisms, restriction to smaller opens, removal of the closed complement, cancellation of the
source inclusion, affine-target shrinking, and general-target shrinking. The final proof takes the
union of all opens where the restriction is finite and applies target-local finiteness.

The proof uses the already stated
`RingHom.exists_finite_awayMap_of_finite_fiber_minimalPrime`; its existing proof hole is the next
algebraic obligation, rather than a new statement in this delivery. The fibre discreteness input,
affine-neighbourhood theorem and closure-specialization input are existing proved declarations.
Updated the existing node's proof, proof dependencies and proof origin to describe the Lean route.
No new public interfaces, definitions, modules or nodes were added, so no consumer adaptation or
interface change record is needed.

Validation: the final module compiled cleanly through `lcompile.py` in 3.4 seconds, with no
warnings. The delivery dry run passed compilation, the declaration/axiom probe and preflight;
review class CODEX because the existing node proof was updated. The public theorem signature
was compared verbatim with the repository copy, and every Lean line is at most 100 characters.

Searches: LeanFinder for a quasi-compact quasi-separated finite-type morphism with finite generic
fibres finite over a dense open; Loogle for `"IsFinite", "IsGenericPoint"`; launcher grep for
`exists.*finite.*away|genericPoints.*preimage|preimage.*genericPoints`; and direct ripgrep of both
library roots and Mathlib. No direct theorem applies. Mathlib's
`exists_isFinite_morphismRestrict_of_finite_preimage_singleton` requires properness, which is absent
here. Mathlib's `SpecMapRestrictBasicOpenIso` supplies the localization coordinates, and the existing
`exists_isAffineOpen_of_subset_genericPoints` handles the empty fibre without an extra case.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers`
(node `lem-weil-pbc-generic-finite-morphism-open-neighborhood`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module. Every private
helper is proved. This is a proof from the declared dependencies, not a decomposition. The already
existing imported theorem `RingHom.exists_finite_awayMap_of_finite_fiber_minimalPrime`
(node `lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away`) remains sorried in its own,
unchanged module; no claim of transitive axiom closure is made for the present theorem.

The proof includes the empty target and empty fibre through the same affine-neighbourhood and
open-cover APIs; it does not assume a nonempty fibre or a reduced target. Nilpotents are handled by
the existing minimal-prime localization theorem. Different generic-point neighbourhoods are united,
not intersected. The Noetherian and compactness hypotheses in the public signature are preserved,
although this argument does not need them.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Pullbacks`: the restriction and quasi-separatedness APIs supply the
  affine reduction without an explicit pullback/tensor-product calculation.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: no direct use; the stated algebra theorem and
  `SpecMapRestrictBasicOpenIso` supply the localization interface.
- `Sheaf.AlgebraicGeometry.FiniteDiscreteFiber`: a retired re-export of the source theorem; use
  `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite` directly instead. This also avoids
  the retired module's unrelated `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` import.

Removed DAG proof dependencies:

- `lem-weil-pbc-open-fibre-product`;
- `lem-weil-pbc-fibre-product-affine-spectra`;
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`.

These describe the explicit diagonal/tensor-product verification of source quasi-separatedness.
The existing Mathlib theorem `quasiSeparatedSpace_of_quasiSeparated` gives that conclusion directly
when the target is affine. The other geometric and algebraic dependencies remain in use, including
basic-open/localization identifications encapsulated by the existing restriction isomorphism.
No blueprint unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect found. The original plan was longer than necessary in its
affine reduction, localization-coordinate bookkeeping and final principal-open refinement. Existing
Mathlib APIs close those steps directly; intersecting the finite neighbourhood with the complement
of the closed image already suffices. The old finite-discrete-fibre import is a retired duplicate,
and its source-library replacement was already recorded in the DAG.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
