# AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeSquare

## Reason

Restore the quarantined module required by the assigned rework row. The live path
`lean/Sheaf/Paper/BoundedExchangeAmbient.lean` is absent; the preserved source is
`quarantine/Sheaf/Paper/BoundedExchangeAmbient.lean`. The rework row records a merge-queue
cluster restore, rather than a mathematical withdrawal. All four public declarations,
their signatures, definitions and proofs are restored. Long archived lines are wrapped,
and the unnecessary private `import all` of MorphismDefs is removed. Its public import
is retained, along with all other public imports, to preserve the archived interface.

## Old

The live module is absent. The archived public definitions are:

```lean
noncomputable def residueExchangeSquare (sq : CommSq g' f' f g) :
    residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f' ≅
      residueExchangeUpperStar Λ f ⋙ residueExchangeUpperStar Λ g' :=
  transportedCompositeIso (residueExchangeUpperStarComp Λ f' g).symm
    (residueExchangeUpperStarComp Λ g' f)
    (congrArg (fun h : X' ⟶ Y ↦ residueExchangeUpperStar Λ h) sq.w.symm)

noncomputable def residueExchangeBaseChange (sq : CommSq g' f' f g) :
    residueExchangeLowerStar Λ f ⋙ residueExchangeUpperStar Λ g ⟶
      residueExchangeUpperStar Λ g' ⋙ residueExchangeLowerStar Λ f' :=
  (mateEquiv (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (residueExchangeSquare Λ sq).hom)).natTrans
```

The archive also proves `residueExchangeBaseChange_counit` and
`boundedConstructibleBaseChange_hom_eq_ambient` with the signatures recorded in their
existing DAG nodes.

## New

The above definitions and both public theorems are restored unchanged at the live path.
There is no alteration to the coefficient ring, scheme hypotheses, composition constraints,
adjunctions or specified base-change morphism. The three existing node attachments and
their proof dependencies remain valid verbatim.

## Users

`tools/downstream.py` with `--allow-missing --uses` reports no live consumers. A search
of the quarantined sources finds the following consumers, which remain quarantined:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | not adapted | Direct public importer; restored API is identical to its archived dependency. |
| Sheaf.Paper.IntegralResidueExchange | not adapted | Uses the bounded comparison theorem through ExchangeAlgebra; signature unchanged. |

No consumer adaptation or withdrawal is made. The direct archived consumer is compiled
as a temporary sandbox check against the restored module (clean, 8.1 seconds).

## Status

landed 20261021T020128-L-2588659 2026-10-21 (merge of deliver/J1/Sheaf.Paper.BoundedExchangeAmbient)
