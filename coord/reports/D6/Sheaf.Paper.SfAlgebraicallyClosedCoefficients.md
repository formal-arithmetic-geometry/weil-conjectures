## What changed

Prove twelve existing obligations in `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`.
Lift and uniquely normalize the integral tensor shift through the fully faithful
intrinsic inclusion. Identify the specified stage system’s
quotient Hom with the abelian-group direct limit and prove additivity, representative
calculus, existence of zero, the distinguished criterion, and common-stage cones.
All public signatures, definitions, and existing public imports are retained.
Private abstract-category helpers avoid expanding the large coefficient constructions.
The proof privately imports the intrinsic integral triangulation interface.
Validation: the complete module compiles through lcompile.py in 26.5 seconds.

## Proved and sorry left

Closed 12 of the original 18 holes (all names have prefix
`WeilConjectures.SfAlgebraicallyClosedCoefficients.`):

- `integralTransitionCommShift_existsUnique`
- `stageTransition_exact`
- `stageTransition_additive`
- `transport_additive`
- `transportSystem`
- `homCoordinates_existsUnique`
- `composition_bilinear`
- `inclusion_additive`
- `representatives`
- `zero_exists`
- `distinguished_iff`
- `commonStage_cone`

Six original holes remain unchanged: `associator_cocycle`,
`stageSystem_existsUnique`, `transitionCommShift_existsUnique`
(node `lem-route-transition-comm-shift-exists-unique`), `transitionExact`,
`shift_existsUnique`, and `transitionIso_commShift`
(node `def-weil-algebraically-closed-coefficients`). No holes are added or split off.
The integral shift theorem is also attached to
`lem-route-integral-transition-comm-shift-exists-unique`; the other closed obligations
are part of `def-weil-algebraically-closed-coefficients`.

## No longer needed

No module is withdrawn and no public import is removed. The integral-shift proof
uses Mathlib `Functor.CommShift.ofComp` directly, so it does not need the newly
stated wrapper `lem-pur-fully-faithful-composite-shift` as a proof dependency.
The other prerequisites for the existing integral functor and comparison remain
needed through those declarations.
The generic proofs are specialized to the intrinsic stages; they do not identify those
stages with the legacy ones. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The common-stage and direct-limit proofs already present in the legacy and general
modules apply to this intrinsic realization as abstract-category arguments. They can
be reused as proved private helpers without importing the general module, which
would create an import cycle. No mathematical statement is changed.
The six remaining coherence, normalization, and shift obligations keep their original
statements and complete proof docstrings. This is a partial proof delivery, with
twelve genuine hole closures and no new obligations.

The complete partial module passes the 60-second compile limit. The remaining scalar
coherence and normalized rational-exactness calculations require further reduction
control; their attempted drafts introduce no delivered declarations or obligations.

During delivery, the integral-shift route node completed stage 1 concurrently.
The packet was refreshed to preserve its reviewed statement, statement dependencies,
status, and other metadata verbatim; only its proof, proof dependencies, and proof
origin are replaced by this implementation.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
