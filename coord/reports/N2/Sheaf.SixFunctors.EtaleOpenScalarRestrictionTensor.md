## What changed

Proved `AlgebraicGeometry.Etale.etaleOpenScalarRestrictionTensor` with its statement,
universes, hypotheses, and public import unchanged. Added private proof imports of
`Sheaf.Paper.EtaleScalarPullbackTensorCoherence`, the private normalization API of
`Sheaf.Paper.ExceptionalCoefficientMaps`, and the private comparison APIs of
`Sheaf.SixFunctors.EtaleOpenTensorDefs` and
`Sheaf.Paper.EtaleProEtaleScalarMateData`.

The proof identifies the two scalar tensor comparisons by their existing uniqueness
property, identifies the fixed open mate with the transported inverse scalar/pullback
comparison, and transports the existing general scalar/pullback tensor law. The
rotation, naturality, interchange and cancellation arguments are fully proved private
helpers. No other module is changed, and no new public declarations or nodes are added.
The item's DAG proof and proof dependencies now describe this route.

## Proved and sorry left

Closed the one assigned hole in
`AlgebraicGeometry.Etale.etaleOpenScalarRestrictionTensor`
(node `lem-coef-etale-open-scalar-restriction-tensor`).
There are zero `sorry` occurrences left in the item, and zero holes added.

This is a complete proof from existing stated dependencies. In particular,
`AlgebraicGeometry.Etale.etaleScalarPullback_tensor`
(node `lem-pur-etale-scalar-pullback-tensor-coherence`) remains an existing imported
obligation; this delivery does not claim to close that dependency or the target's
entire axiom closure. No split-off statements are introduced.

## No longer needed

No existing Lean import is removed, and no module is withdrawn or claimed globally
pruned. The old plan's direct proof dependencies
`lem-pur-derived-change-of-rings`
(`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`) and
`lem-weil-pbc-site-derived-tensor-descent`
(`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`)
are unnecessary as direct dependencies of this proof: their representative descent
work is already encapsulated by the general scalar/pullback tensor law. They may
remain needed elsewhere or transitively. The proof also does not use the thick-locus
assertion of `lem-coef-etale-hom-thick-locus`
(`Sheaf.SixFunctors.EtaleHomThickLocus`); it uses the tensor model comparison's
uniqueness theorem directly. The original statement dependency and public import
are preserved. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned new degreewise/K-flat proof duplicates an existing general theorem:
`etaleScalarPullback_tensor` already states the normalized compatibility for arbitrary
scheme morphisms and arbitrary coefficient maps. Exact open restriction follows by
proved categorical transport, with no new descent obligation. No mathematical
statement was weakened or repaired. The current server queue identifies this as a
one-hole proof item; the older quarantine record does not require a declaration rename.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.EtaleOpenScalarRestrictionTensor": "a8752c02bd02a09b72042fc4752ea3bad13eca0f"}, "results": {"Sheaf.SixFunctors.EtaleOpenMixedTensorScalar": {"hash": "48d111a2e2ec4fefe32412f6cd68e1df556c298e", "status": "OK"}}, "seconds": 89, "time": "2026-10-28T00:39:36+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
