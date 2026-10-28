## What changed

Replaced the proof hole in `clopen_structural_comparison_prefix` by a construction of
its total comparison from the ordinary braided restriction. Coproduct preservation
comes from the already proved `clopen_structural_coproduct_adjunction`; transport
along `ULift` supplies the exact integer total-degree index types.

The comparison is `Functor.uncurry.mapIso` of the canonical
`mapBifunctorComparisonNatTrans` induced by the ordinary inverse tensorator.
This is the underlying construction of `mapHomologicalComplexδNatTrans`. Its summand equation is the existing
`map_ιMapBifunctor_mapBifunctorComparisonX`. Its differential equation follows by
moving the differential across this chain map, applying the summand equation,
and applying `CochainComplex.ιTensorObj_d` to the restricted complexes.
The construction uses the same explicit tensor instances as `coefficientTotalTensor`;
an irreducible wrapper prevents repeated unfolding of those data. A delivery recheck
exceeded 60 seconds despite an earlier 44-second compile. Profiling identified the
comparison construction and kernel checking as the main cost. After supplying explicit
instances and the irreducible wrapper, the proved comparison construction and its summand
formula were factored into `ProEtaleClopenTotalTensorComparison` to bound each file
separately. No time limit or linter is disabled. Profiling options are removed for delivery. The final import-order compile passed:
ordinary normalization 2.8 seconds, proved total comparison 30.4 seconds, and the item
20.9 seconds.
No tensor object, differential, restriction functor or target statement is changed.

A new module `Sheaf.AlgebraicGeometry.ProEtaleClopenOrdinaryTensorNormalization`
states only the normalized braided structure on ordinary module sheaves along a
single clopen immersion. It contains no cochain complexes or total comparison.
The item imports it and the existing coproduct-adjunction theorem privately.
The ordinary tensorator is a property of the single immersion; disjointness and covering
are used for the existing coproduct-preservation result.

## Proved and sorry left

Closed the textual hole in
`AlgebraicGeometry.Scheme.ProEt.clopen_structural_comparison_prefix`
(node `lem-pur-clopen-structural-comparison-prefix`).

Added one named hole:
`AlgebraicGeometry.Scheme.ProEt.clopen_ordinary_tensor_normalization`
(node `lem-pur-clopen-ordinary-tensor-normalization`). This is a decomposition,
with one upper hole replaced by one strictly smaller ordinary-sheaf obligation,
not a net reduction of the hole count. The total-complex comparison and its two
normalization clauses have complete proofs. The item has zero remaining holes;
the new module has one. No existing dependent proof was replaced by a hole.

The remaining lemma is true for the empty component, zero coefficient ring,
and arbitrary module sheaves: restriction commutes with the presheaf tensor and
with module sheafification. The docstring explains how the unit-compatible
comparison supplies the normalized strong braided structure.

## No longer needed

No existing import, node or module is withdrawn. The support-data dependency stays.
The parent no longer needs a separate local-generator proof for the total summand
or signed differential clauses: the existing totalization comparison and differential
APIs prove them directly. No additional coherence or differential node is introduced.

## Where the brief, the DAG or earlier work was wrong

The old plan grouped the ordinary tensorator construction, totalization and signed
differential calculation into one local-generator verification. They are distinct:
the complex-level construction follows from standard totalization APIs once the
ordinary braided structure and coproduct preservation are given. The DAG now
records that argument, including the already proved coproduct-preservation node.

The clopen normalization modules farther up the library import this item through
the structural-data theorem, so using those results here would be circular.
The existing module-sheafification restriction theorem gives the relevant method,
but its statement is for small sites with equal site and coefficient universes;
it does not directly instantiate to the current pro-etale universes.

The recorded unit has no realized statement or steps, and its old
`sk-def-purity-conv/_section.md` path is absent from the current blueprint snapshot.
No unit or chapter route is changed.

## New nodes

`lem-pur-clopen-ordinary-tensor-normalization` records the ordinary sheaf-level
braided tensorator with its pure-tensor normalization for a single clopen immersion.
Its proof plan uses sectionwise presheaf tensors, continuous and cocontinuous
restriction, the sheafification unit comparison, and monoidal localization.
It is strictly smaller than the item: no total functor, total summands, signed
differential or complexes occur in its statement. The proved support node `lem-pur-clopen-total-tensor-comparison` records the canonical
total comparison and its summand formula, with zero holes. There are no change records,
since no other existing module or statement is changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleClopenOrdinaryTensorNormalization": "d70f2f9838bd25e9ad0a2627b2c044880d97bf63", "Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparisonPrefix": "f5491543cea4e5fd860d9f114444702bcaa2528e", "Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorComparison": "34fa17a5b60c8f284c975c85f4f4d5ef3252ce97"}, "results": {"Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparison": {"hash": "9e0bbd7ce6b6ceba81e20c9512e85f523f46313b", "status": "INFRA"}, "Sheaf.AlgebraicGeometry.ProEtaleClopenStructuralComparisonSymmetry": {"hash": "aefb081ba82bc8ca083b0ebd8d3f6303d7e34ab5", "status": "OK"}}, "seconds": 130, "time": "2026-10-28T08:14:00+0800", "transitive": 0, "version": 1}
```

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
