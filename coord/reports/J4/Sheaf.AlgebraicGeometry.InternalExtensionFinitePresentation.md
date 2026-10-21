## What changed

Proved `AlgebraicGeometry.ProEtale.internalExtension_finitePresentation` in
`Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation`, with its signature unchanged.
The regular comparison is the mixed-bimodule right unitor, forgetting the right action.
The underlying object and left action agree definitionally with scalar extension of the
regular module; the quotient equation is `coequalizer.π_desc`.
Finite-free comparisons compose `Functor.mapBiproduct` and `biproduct.mapIso`.
Cokernel comparisons compose `PreservesCokernel.iso` and `cokernel.mapIso`.
Mapping a presentation isomorphism and composing gives the finite-presentation witness.

The node records these implementations and uses existing abelian, additive and colimit
preservation instances instead of separately invoking the two general infrastructure lemmas.
The unit route and all five mathematical steps remain intact. No declarations or source-library
files were added or changed. No statements or definitions were changed.

Validation: the complete module compiles through `lcompile.py` with no errors or warnings
(3.2 seconds). All finite ranks, including zero, are handled uniformly by the finite biproduct
API. No flatness, kernel preservation, or nonzero-ring assumption is used.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.internalExtension_finitePresentation`
(node `lem-sfb-internal-extension-finite-presentation`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean file.
This is a proof, not a decomposition.

## No longer needed

Removed the proof-only imports:

- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`: scalar extension's
  colimit-preservation instance already comes from `ModuleObjects.ExtendScalars`.
- `Mathlib.CategoryTheory.Monoidal.Bimod`: already publicly available through
  `ModuleObjects.ExtendScalars`.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: no separate colimit-to-additive
  argument is needed; scalar extension already has a direct Additive instance.

Removed direct proof dependencies `lem-sfb-grothendieck-sheafification` (and its tool approval)
and `lem-sfb-preserving-colimits-additive`. Existing ambient instances suffice. This proof does
not require importing `Sheaf.CategoryTheory.GrothendieckSheafification`. These removals concern
this node's proof only; other parents may still need the nodes, and no module is withdrawn.
All other declared dependencies, including internal extension right exactness, are retained.
The five public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The plan overestimated the separate infrastructure
needed in step 1: ambient instances and scalar extension's direct additivity and colimit
preservation are already available. Its finite-free and cokernel argument is valid as stated.
The shorter Mathlib search found ordinary module presentations rather than the requested internal
module theorem; Mathlib's general biproduct and cokernel isomorphisms implement the plan directly.
No change record or consumer adaptation is needed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
