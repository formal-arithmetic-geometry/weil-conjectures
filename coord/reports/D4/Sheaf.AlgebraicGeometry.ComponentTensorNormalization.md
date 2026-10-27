## What changed

Replaced the proof hole in `Sheaf.AlgebraicGeometry.ComponentTensorNormalization` by a
reduction to the integral-function detection step on pairs of free relative-test sheaves.
All existing public declarations, definitions, signatures and public imports are unchanged.

The proof constructs the two tensor-bifunctor transformations in the original equation.
Naturality of scalar action proves the correction's unit equation. The two left-unit laws
then prove the tensor equation when the first argument is the tensor unit. For free test
pairs, postcomposition with the inverse canonical tensorator and the new detection lemma
reduce the comparison to the unit-unit equation. Finally, Mathlib's separating free-sheaf
family and the adjunctions for inverse image and target tensoring extend the equality to
arbitrary sheaves. This last extension is proved directly, with no presentation or
coequalizer lemma left unproved.

Added one proof import for `Sheaf.AlgebraicGeometry.ComponentFreeTensorDetection` and
proof imports for the generator, tensor bifunctor and monoidal closedness APIs. Updated
the item's proof plan and added the detection node. No source-library file is changed.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.ProEtale.CondensedRing.component_unit_normalized_tensor`
(node `lem-zl-component-unit-normalized-tensor`) by a complete Lean proof from the new
lemma. The item module has zero remaining holes.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.component_free_tensor_detection`
(node `lem-zl-component-free-tensor-detection`) in the new module
`Sheaf.AlgebraicGeometry.ComponentFreeTensorDetection`.

This is a decomposition: one upper hole closed and one strictly narrower mathematical
step left, for net zero holes closed. The remaining statement involves only maps into
tensors of free test sheaves and their integral-function evaluations. It has no supplied
monoidal structure, braided structure, correction, or tensor-normalization conclusion.
Every private helper is proved. No hole occurs in a definition.

## No longer needed

No existing module or import is withdrawn. None is claimed pruned.

The original final step's explicit coproduct/coequalizer presentation construction is
unnecessary: free sheaves form a separating family, and the relevant source bifunctor
is separately a left adjoint. The proof uses Mathlib separation and adjunction
hom-equivalences directly. The relative-test theorem remains needed through the fixed
inverse-image definition, canonical tensor structure and detection lemma; it is not
claimed pruned. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The two listed dependencies construct the relative site and inverse image but do not
state the finite-clopen detection result used by the original proof plan. They cannot
by themselves discharge that step by applying a named declaration. The new lemma
isolates precisely the missing separation assertion, rather than repeating the
arbitrary-structure normalization statement under another name.

The informal detection argument must not assert that pointwise equality of finitely
many profinite coordinates persists on an open neighborhood. Its corrected proof uses
the finitely many closed profinite coincidence loci indexed by partitions of the finite
summand set. Their component pullbacks give a finite jointly surjective pro-etale cover,
on which the sum cancels block by block. Empty tests and empty bases give zero free
sheaves. Neither a point nor nonemptiness is assumed.

## New nodes

`lem-zl-component-free-tensor-detection`: maps into a tensor of two pulled-back free
relative-test sheaves are detected by tensoring the inverse images of all maps of the
two free sheaves to the integral unit. The node and docstring give the free-sheaf
identification, finite-clopen coefficient separation, and closed-locus cover proof.
The construction is grounded in HRS (4.1) and Bhatt--Scholze Lemma 2.2.8; the extraction
and separation proof are attributed to this worker. Searches found Mathlib free sheaves,
separating generators and solidification definitions, but no matching detection theorem.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
