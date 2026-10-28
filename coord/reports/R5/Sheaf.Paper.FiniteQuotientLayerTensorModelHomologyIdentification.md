## What changed

Added the missing coefficient-isomorphism hypothesis `hφ` to
`finiteQuotient_layer_tensor_model_homology_identification` and proved the corrected
statement by transporting through the exact derived change, the canonical homology
comparison for mapped complexes, and exact chart restriction. The proof uses private
helpers for the coefficient-change equivalence and constant-realization exactness.
Adapted `Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison` at its sole call to
pass the importer’s existing `hφ` hypothesis.

## Proved and sorry left

Closed the sole sorry in
`AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_model_homology_identification`.
No sorry was added; zero sorries remain in the delivered modules.

## No longer needed

The proof does not use `lem-weil-pbc-site-derived-tensor-descent` or
`def-weil-pbc-ringed-derived-restriction` (the coefficient map is an isomorphism, so the
derived change is computed termwise without a K-flat descent argument); the node's
`proof_deps` now list the nodes actually used (reviewer FIX). The unused imports
`Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`,
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction` and
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived` were removed (reviewer FIX).
The temporary exploratory import of
`Sheaf.Paper.FiniteQuotientPreviousLocalComplexesChartHomology` was removed; the required
helper proof is local and private.

## Where the brief, the DAG or earlier work was wrong

The original theorem statement was too strong: it asserted ordinary homology after a
potentially non-flat derived scalar change without assuming that the coefficient maps
are isomorphisms (or imposing a K-flat/projective hypothesis on the complex). The
existing `FiniteModelCoefficientTransport` module records the same missing-flatness
problem. The node was corrected with a `statement_change` record; its sole citer
already had `hφ`, so its mathematical use remains valid after the forced call-site
adaptation.

## Forced adaptations

### Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison (holder P3)

Against the changed item, the original call
`finiteQuotient_layer_tensor_model_homology_identification X d φ n Z P q`
failed because Lean now required the new `hφ` argument. The adapted line passes
`hφ`:
`finiteQuotient_layer_tensor_model_homology_identification X d φ hφ n Z P q`.
This is the only changed line and is forced by the corrected theorem signature; the
adapted module compiles together with the item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison": "e7e22bda9763d91570b3c4729f81fe18fbffc15b", "Sheaf.Paper.FiniteQuotientLayerTensorModelHomologyIdentification": "349dafa52e10823388e27f9f3e151ab700472527"}, "results": {"Sheaf.AlgebraicGeometry.DiscreteConstantPresentationLifting": {"hash": "858429f71b9670b1576d281d5ef61632c572f34a", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T08:12:06+0800", "transitive": 1, "version": 1}
```

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
