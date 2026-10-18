## What changed

Replaced the single sorry in `lean/Sheaf/Paper/AdditiveTotalTransport.lean` with a
complete proof of `HomologicalComplex₂.additive_total_transport`. The proof uses
`hasTotal_of_isStrictlyLE B b 0` and `preservesTotal_of_isStrictlyLE B b 0 F`
for the original bicomplex, repeats these constructions with the independent bound
`b'` for the second bicomplex, obtains the comparison's `IsIso` instance, and applies
`mapTotalIso_hom_naturality`. The explicit comparisons reduce definitionally to
`mapTotalIso`. Signatures, definitions, imports, and the DAG route are unchanged.

The existing source argument in BicomplexColumns.lean:874–912 supplies finite
support and preservation, including the empty diagonal, using the finite-coproduct
preservation instance recorded by the first proof dependency. TotalComplexMap.lean:
117–145 supplies the chain isomorphism and naturality recorded by the second.
The unit's route is unchanged. LeanFinder returned generic bicomplex functors;
Loogle found `Functor.preservesFiniteCoproductsOfAdditive`; source searches found
the exact bounded-total and comparison declarations used here.

## Proved and sorry left

Closed: `HomologicalComplex₂.additive_total_transport`
(node `lem-sfb-left-resolution-additive-total-transport`), 1 of 1 original holes.
Added: none. Remaining sorry declarations in the delivery: none. No split-offs.
The existing definition `HomologicalComplex₂.additiveTotalComparison` is unchanged.

## No longer needed

None. Both existing imports are used. Both declared proof dependencies remain
needed: finite-coproduct preservation underlies `preservesTotal_of_isStrictlyLE`,
and the total comparison dependency supplies `mapTotalIso` and its naturality.
No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing declarations prove the stated plan directly with column bound
zero. No additional hypotheses, statement changes, or new definitions are needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
