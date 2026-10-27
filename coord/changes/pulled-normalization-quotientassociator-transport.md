# AlgebraicGeometry.Scheme.PulledNormalization.quotientAssociator

## Reason

The legacy normalization composed the scalar isomorphism with an equality isomorphism
of chosen derived functors. Component conversions then evaluated that chosen data and
exceeded the 60-second file limit. Transport the whole isomorphism along the coefficient
map equality instead. The private theorem `quotientAssociator_legacy_eq` proves that the resulting
isomorphism equals the complete legacy construction, including its normalization.
The full candidate proof compiled in 59.0 seconds before unused-helper cleanup.

## Old

```lean
def quotientAssociator
    (nrm : ScalarNormalization X)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    reductionDerivedChange X (reductionCoefficientMap X d c b hbc) ⋙
        reductionDerivedChange X (reductionCoefficientMap X d b a hab) ≅
      reductionDerivedChange X (reductionCoefficientMap X d c a (hab.trans hbc)) :=
  scalarAssoc X nrm (reductionCoefficientMap X d c b hbc)
      (reductionCoefficientMap X d b a hab) ≪≫
    eqToIso (congrArg (fun f ↦ reductionDerivedChange X f)
      (reductionCoefficientMap_comp X d c b a hab hbc))
```

## New

```lean
def quotientAssociator
    (nrm : ScalarNormalization X)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    reductionDerivedChange X (reductionCoefficientMap X d c b hbc) ⋙
        reductionDerivedChange X (reductionCoefficientMap X d b a hab) ≅
      reductionDerivedChange X (reductionCoefficientMap X d c a (hab.trans hbc)) :=
  Eq.ndrec (motive := fun q ↦
    reductionDerivedChange X (reductionCoefficientMap X d c b hbc) ⋙
      reductionDerivedChange X (reductionCoefficientMap X d b a hab) ≅
        reductionDerivedChange X q)
    (scalarAssoc X nrm (reductionCoefficientMap X d c b hbc)
      (reductionCoefficientMap X d b a hab))
    (reductionCoefficientMap_comp X d c b a hab hbc)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PulledReductionNormalizationComparison | E9 | Preserve the signature and value; use the transported comparison's proved representative and coherence formulas. |

`tools/downstream.py Sheaf.Paper.PulledReductionNormalizationComparison --uses
AlgebraicGeometry.Scheme.PulledNormalization.quotientAssociator` lists zero downstream modules and this module as the only textual user.
No other Lean module needs adaptation. The unfinished DAG parent
`lemma-weil-pbc-completed-pullback-reduction` remains dependent on this node;
no parent, unit route, or source-library declaration is withdrawn.

The changed data occur in this node's `Comparison` statement, so the independent
statement review must check this definition against the source again. The named
legacy equality proves the data unchanged mathematically. No `Challenge.lean`
signature or definition is edited; there is currently no downstream Lean module
whose target statement uses this definition.

## Status

landed 20261022T113936-L-421545 2026-10-22 (merge of deliver/E9/Sheaf.Paper.PulledReductionNormalizationComparison)
