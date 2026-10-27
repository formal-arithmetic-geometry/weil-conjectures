## What changed

Filled `AlgebraicGeometry.Scheme.Modules.exists_affine_fibre_support_model` in
`Sheaf.AlgebraicGeometry.AffineFibreSupportModel` without changing its signature.
The proof chooses affine neighbourhoods, applies the existing finite-presentation
supporting-subscheme theorem, constructs the canonical fibre maps by pullback,
and proves the support and local-dimension comparisons. Three proved private
helpers handle local dimension under open embeddings, corestriction of the
support embedding, and the open fibre map with its two projection equations.

Added proof imports of `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`
and `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback`.
Updated the item's DAG proof, dependencies and proof origin to match the Lean.
No existing external module, statement, definition or public import was changed.

Validation: `lcompile.py` compiled the final module successfully in 8.3 seconds.
The original theorem signature is unchanged and every Lean line is at most
100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_affine_fibre_support_model`
(node `lem-trf-affine-fibre-support-model`). There are zero remaining holes in
this module, zero added holes, and zero split-off statements.

The proof uses the already stated
`exists_finitePresentation_closedImmersion_fiber_support` from
`Sheaf.AlgebraicGeometry.FiniteTypeSheafFinitePresentationSupport`; its existing
hole is unchanged. Thus this is a proof from the stated dependencies, rather
than a claim that the complete transitive axiom closure is finished.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Separated`;
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, replaced by the
  tensor-pullback quasi-coherence API.

Removed direct proof dependencies:

- `lem-weil-pbc-lft-pointwise-criterion`: the existing restriction and composition
  instances give local finite type directly;
- `lem-weil-pbc-dimension-at-point-open-subspace`: the private helper proves the
  open-embedding dimension comparison directly from the neighbourhood infima;
  its obsolete tool-use entry was removed;
- `def-pc-module-pullback`: no comparison of successive pullback functors is
  needed in this proof. Their support sets are computed by the existing finite
  type support-pullback theorem instead.

The ordinary quasi-coherent pullback lemma remains indirectly used through the
proved tensor-pullback comparison. No module is withdrawn, and no claim is made
that these generic dependencies become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned comparison by pullback composition and restriction stalks is
unnecessary: `finiteType_module_support_pullback` computes all the required
support sets as inverse images. The rest of the stated affine/support route is
retained, including the supporting-subscheme input and the unit route.

Edge cases checked: the hypothesis excludes the zero module and an empty source;
no closedness of the chosen point, reducedness of the supporting subscheme,
Noetherian hypothesis on the base, or global quasi-compactness/separatedness is
used. The supporting fibre maps keep both required projection equations.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
