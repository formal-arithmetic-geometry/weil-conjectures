## What changed

Filled the four original theorem proofs, preserving every existing public signature and definition.
A private generic proof constructs the fixed-pair truncation functors from the source library's
proved t-exact truncation comparisons. Naturality proves the first two equivariant arrows;
`Functor.eTruncGEδLT_comm` proves the boundary equation. Composed truncations and shift give
cohomology in the heart.

The geometric inputs are the existing automorphism shift/descent theorem and isomorphism
field-transport theorem. Exact inverse image preserves integral homology vanishing, hence
both rational standard classes. Finite-stage representatives give the common-stage argument.
Private comparison constructions retain the specified object equalities and signed shifts.
The point proofs apply the fibre functor to the Weil-morphism equation, use the recorded
transport naturality with its object identifications, then apply coefficient cohomology.

Updated the node's proof, proof dependencies and origin to match this route. No other module
is changed. No new public declaration, module, node, axiom, or hole is introduced.

## Proved and sorry left

Closed the four original holes:

- `WeilConjectures.fixedPairRationalTruncationCohomology`
- `WeilConjectures.fixedPairCommonTruncationCohomology`
- `WeilConjectures.fixedPairRationalPointCohomology`
- `WeilConjectures.fixedPairCommonPointCohomology`

Holes added: zero. Holes left in the delivered module: zero. The cited existing theorem
statements are used as dependencies; their proofs are separate project items.

Validation: the final module compiled with exit code 0 and no warnings (59.4 seconds).
Checked the original public signatures and definition bodies byte for byte. The construction
is uniform in every cutoff and shift, including zero objects and Frobenius equal to identity;
the point calculation uses only functoriality and holds for every Weil morphism.

## No longer needed

The proof does not use these former proof dependencies:

- `lem-pod-semilinear-field-operation-lifts`: existing automorphism signed-shift descent
  supplies exactness, and isomorphism field transport supplies preservation of standard classes.
- `lem-pod-texact-truncation-comparison`: use the already proved source-library `eTrunc` API.
- `lem-a1-fixed-pair-truncation-orthogonality`: `IsoAlgebra.mapOfNatIso` and naturality suffice
  for precisely the lift and equivariance clauses stated in this module.
- `lem-pod-fixed-pair-postnikov-identifications`: the stated cohomology clause is the
  definitional composition of the two lifts and the shift; standard shift bounds prove heart
  membership. No absorption or interchange clause occurs in the Lean statement here.
- `lem-pod-texact-truncation-triangle-comparison`: the source library already proves the
  exact boundary compatibility as `Functor.eTruncGEδLT_comm`.

Removed obsolete `tool_uses` entries `lem-weil-heart-short-exact-triangles` and
`lem-a1-fixed-pair-truncation-orthogonality`, neither of which the proof calls.

Removed private imports `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`,
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`,
`Sheaf.Paper.SfDerivedDirectImage`, and `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
The first is replaced by its proved source API; the latter three supply no declaration used
by these statements or proofs. Existing public imports are retained. No module is withdrawn;
other consumers may still need every dependency listed above.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned fixed-pair orthogonality, Postnikov and triangle
packages are stronger than the clauses actually stated in this module. The source library
already supplies the needed t-exact boundary comparison. The existing normalized automorphism
shift theorem covers geometric Frobenius directly, without the separatedness hypotheses
of the semilinear-operation package. These observations allow the shorter assembly recorded
in the updated node.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
