## What changed

Proved `AlgebraicGeometry.ProEtale.directImageChangeRingTranspose` in
`Sheaf.Paper.DirectImageChangeRingTranspose` from the declared normalization and
coefficient-adjunction theorems. Added private proof imports of
`Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization` and
`Sheaf.Algebra.Homology.RingedDerivedTensorNative`.
A concrete private tensor model supplies the normalization theorem's model parameters;
its tensor and representative comparison are the native derived tensor constructions.
The chain isomorphism's hom supplies the requested normalized representative.
The transpose equality applies the existing coefficient-adjunction Hom identity.
Naturality follows by transposing gamma, using tensor/pullback and counit naturality,
then applying restriction and naturality of the direct-image comparison.
Existing statements, definitions, and public imports are unchanged.

Validation: the entire module compiled on the project server in 13.5 seconds.
A line-length warning was corrected before the final delivery checks.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.directImageChangeRingTranspose`
(node `lem-sp-direct-image-change-ring-transpose`).
No holes remain in the delivered module, and no holes were added or split off.
The proof uses the already stated theorem
`AlgebraicGeometry.ProEtale.proEtaleScalarTensorNormalization`, whose existing hole
remains in its own module; its proof is not duplicated or moved in this delivery.

## No longer needed

None. The existing dependency route is retained; the DAG records the native tensor
presentation additionally used to instantiate the normalization theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The two published names `tensorPullbackIso` and
`directImageScalarPullbackIso` unfold to the same canonical comparison; proof
irrelevance identifies their coefficient-square witnesses. The normalization theorem
has tensor-model parameters even though the representative conjunct used here does
not mention those parameters, so the proof constructs native tensor presentations.
No properness, boundedness, or flatness of B over A is used in the categorical
assembly. Zero complexes, identity coefficient maps, the empty scheme, and nonflat
finite coefficient quotients are covered by the unchanged normalization statement.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
