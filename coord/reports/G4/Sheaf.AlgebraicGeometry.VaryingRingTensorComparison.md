## What changed

Prove `AlgebraicGeometry.ProEtale.VaryingRing.tensorComparison_exists` without
changing its statement or public imports. Construct the ringed-site pullback on
the vertical sequence site and retain the normalized underlying hom-equivalence
when restricting its adjunction to linear maps. Transport the ordinary tensor
comparison to the specified exact left adjoint by adjoint uniqueness. Its
transpose is checked on pure tensors against the supplied section formula.
Total the inverse ordinary comparison and descend it through the given tensor
models on flat-term K-flat representatives.

Private helpers retain the normalized linear adjunction, descend the ordinary
comparison, and transport tensor naturality and adjunction transposes. A private
irreducible `transportedOrdinary` constructs the comparison as the composite of
the adjoint-uniqueness isomorphism, the normalized tensorator, and the tensor of
the two adjoint-uniqueness components. Its proved naturality and cancellation
equations keep the geometric proof from repeatedly unfolding that composite.
The abstract ordinary-transpose calculation takes the functors and insertion
maps as parameters, so it does not unfold the geometric construction while
checking the pure-tensor equation.

Proof-only imports expose the existing normalization, scalar-extension, K-flat
preservation and representative-descent APIs. The node proof and dependency list
record these constructions.

The proof-context and private-construction record is
`coord/changes/G4-varying-ring-tensor-private-constructions.md`.

## Proved and sorry left

Closed the one original hole,
`AlgebraicGeometry.ProEtale.VaryingRing.tensorComparison_exists`
(`lem-pur-varying-ring-tensor-comparison`). It adds no holes or split statements.
Proved 1 of 1 original sorries;
zero sorries remain in the item and zero are added elsewhere. The complete
module compiled through `lcompile.py` in 48.7 seconds. The delivery runs the
required independent preflight and consumer checks.

## No longer needed

None of the original declared proof dependencies is removed. No module is
withdrawn. The proof uses the general ringed-site construction directly; a
separate identification of each pulled-back constant coefficient ring is not
needed. No original import is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan did not expose the normalized module hom-equivalence needed
for the exact transpose equation. The private adjunction helper records that
formula from the existing linear-mate construction. The derived descent uses
flat-term K-flat representatives in the source and all K-flat representatives in
the target, so it does not require an extra flat-terms preservation assertion.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
