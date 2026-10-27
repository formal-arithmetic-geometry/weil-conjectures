## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_of_isClosedImmersion`
in `Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion` by applying the proved
`isAmple_tensorPullback_of_isAffineHom i M hM`. Mathlib infers affineness of the
closed immersion. The absolute ampleness notion, every hypothesis, and the explicit
invertibility instance in the conclusion are unchanged. Replaced the old private
section-pullback proof import by `WeilConjectures.AlgebraicGeometry.AmplePullback`.
Preserved the existing public imports and importer-visible interface.

Validation: `lcompile.py` compiled the delivered Lean file cleanly (3.9 seconds);
`import_direction.py may` accepted the new private proof import.

Updated the item's proof, proof dependencies, and proof origin to this specialization.
The graded-immersion unit still invokes precisely this closed-immersion restriction
result in Step 3; no unit step is bypassed. The existing proved affine-pullback
result is used as a tool. Identity immersions, the empty source, arbitrary quotient
ideals, and nonreduced closed subschemes require no extra hypotheses.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_of_isClosedImmersion`
(node `lem-trf-ample-restrict-closed-immersion`).

Zero holes remain in the item; zero holes added; zero split off.
The affine-pullback theorem used has a complete proof in the current source.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback`.
Its result is used internally by the affine-pullback theorem, so the module remains
needed transitively and is not proposed for withdrawal.

The item's proof no longer directly needs these former planned dependencies:

- `lem-weil-pbc-invertible-pullback-invertible`: invertibility is already handled
  by the affine-pullback result and the unchanged statement's tensor instance.
- `def-weil-pbc-ample-invertible-module`: no unfolding is needed in the new proof;
  it remains a statement dependency.
- `lem-weil-pbc-closed-in-quasi-compact`: quasi-compactness is handled by the
  affine-pullback theorem.
- `lem-weil-pbc-tensor-power-section-nonvanishing-pullback`: section transport is
  handled internally by the affine-pullback theorem.
- `lem-weil-pbc-closed-immersion-affine-cover-criterion`: only the existing
  Mathlib instance from closed immersion to affine morphism is needed directly,
  already covered by `def-weil-closed-immersion`.

No modules are withdrawn. Shared dependencies may remain needed by other proofs.

## Where the brief, the DAG or earlier work was wrong

The three-step planned argument is valid but unnecessary here: the already proved
absolute affine-pullback theorem subsumes it. Earlier independent reviews of this
node explicitly identified this specialization. The DAG now records the proof
actually used. No statement or definition repair was necessary.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
