# AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_exchange_square

## Reason

Restore the nonempty module required by its current rework row. The live source is absent
following the merge queue cluster restore; the preserved archive is
`quarantine/Sheaf/Paper/IntegralResidueExchangeAlgebra.lean`. This is restoration, not
withdrawal. Preserve the original public theorem, public import and DAG attachment.
Specialize the final proof through the current pointwise coefficient-exchange theorem;
the pull cube and both actual mate counit equations are supplied at the objects needed.

## Old

The live module is absent. Its archived public theorem has the following signature
in the unchanged namespace, universe and variable context:

```lean
theorem integralResidue_exchange_square (sq : CommSq g' f' f g)
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    (c.pull g).hom.app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g).map
        ((c.push f).app K) ≫
      (residueExchangeBaseChange
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq).app
        ((residueExchangeReduction ℓ E X).obj K) =
    (residueExchangeReduction ℓ E Y').map
        ((residueExchangeBaseChange (integralCoeff ℓ E) sq).app K) ≫
      (c.push f').app ((residueExchangeUpperStar (integralCoeff ℓ E) g').obj K) ≫
      (residueExchangeLowerStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f').map
        ((c.pull g').hom.app K)
```

## New

Restore exactly this signature and the original public import of
`Sheaf.Paper.BoundedExchangeAmbient`. The private `pull_transport` and `pull_square`
proofs are preserved; the final proof now uses
`CategoryTheory.Adjunction.coefficient_exchange_of_counit_at` instead of the universal
wrapper. No definition, hypothesis, specified comparison morphism or target changes.
The original DAG attachment and all four proof dependencies are retained.

## Users

`tools/downstream.py --allow-missing --uses` reports zero live consumers. Searching
both live and quarantined Lean sources finds the following archived direct consumer;
its DAG node still uses this result, so it must remain available.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueExchange | not adapted; quarantined | Uses the same equality at `M.obj` to build an arrow isomorphism; signature and mathematical meaning are preserved. |

The original archived consumer compiles in 44.8 seconds against the restored module,
with only its four pre-existing long-line warnings. It is a temporary sandbox check
and is not in the delivery set; no consumer is changed.

## Status

landed 20261021T021925-L-2793645 2026-10-21 (merge of deliver/V1/Sheaf.Paper.IntegralResidueExchangeAlgebra)
