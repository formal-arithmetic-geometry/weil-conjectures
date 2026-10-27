## What changed

Filled five existing theorem proofs in `Sheaf.Paper.CanonicalTateComparisons`:
`integralGood`, `finiteGood`, `integralTensorUnit_isIso`,
`ordinaryReductionSquare_existsUnique`, and `ordinaryPulledLine_kflat`.
The goodness proofs specialize flat-single normalization. The tensor-unit proof
uses intrinsic completeness of the existing integral line and the normalized
Roos completeness criterion. The ordinary reduction square uses uniqueness of
left adjoints to the normalized direct-image restriction square. The final
K-flatness proof tensors the existing line pullback isomorphism with each acyclic
test complex and transports acyclicity from `integralGood`.

Added private proof imports for these interfaces and their coefficient datum, plus
a proved private functorial-composition helper. Scoped irreducibility settings keep
the tensor proof from expanding the large completion and total-tensor constructions.
Updated the existing node's proof, proof dependencies, and proof origin.
The final file compiled cleanly through `lcompile.py` in 59.2 seconds; all
diagnostic profiling options were removed.

## Proved and sorry left

Closed five of the eleven holes present at the start, with no holes added or split
off. The closed declarations, in namespace `WeilConjectures.CanonicalTate`, are:

- `integralGood`
- `finiteGood`
- `integralTensorUnit_isIso`
- `ordinaryReductionSquare_existsUnique`
- `ordinaryPulledLine_kflat`

Six original holes remain, all owned by
`def-pur-canonical-tate-comparisons`:

- `WeilConjectures.CanonicalTate.finitePullSheaf_existsUnique`
- `WeilConjectures.CanonicalTate.integralProductComplex_existsUnique`
- `WeilConjectures.CanonicalTate.finiteProductComplex_existsUnique`
- `WeilConjectures.CanonicalTate.integralPullUnit_isIso`
- `WeilConjectures.CanonicalTate.finiteScalarSheaf_existsUnique`
- `WeilConjectures.CanonicalTate.commonProduct_existsUnique`

The three previously completed proofs are retained. These five proofs use the
existing declared dependencies; this delivery does not assert that their full
transitive axiom closures are already sorry-free.

## No longer needed

Removed the exploratory proof imports `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor`
and `Sheaf.Paper.SignedLineTensorEquivalence`: pulled-line K-flatness follows directly
from `integralGood` by tensoring an isomorphism. Their nodes are not needed as direct
dependencies of this argument. No original import, module, or unit step is withdrawn.
The partial node's
remaining six existence and augmentation assertions remain needed by the actual
comparison definitions. The new proofs require no new mathematical statements.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The node's previous final proof step
recorded eleven unproved lemmas; it now records the five additional arguments and
names the six remaining holes. No signatures, definitions, public imports, or
source-library declarations were changed.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
