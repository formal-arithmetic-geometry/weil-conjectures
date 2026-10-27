# AlgebraicGeometry.ProEtale.purZlPointReduction

## Reason

Repeated kernel checking of the large completed-comparison choice predicate exceeds
the file limit. Extract its normalized integral cone as a fully proved theorem,
then choose from this smaller predicate. Normalization uniquely determines every
component by restriction to singleton profinite sets and the finite constant
comparison, as proved in the item. Thus the mathematical map and all targets retain
their meaning. The definition is irreducible with its generated equation API.

## Old

```lean
noncomputable def purZlPointReduction (ℓ : ℕ) [Fact ℓ.Prime] :
    (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ℓ])) ⟶
      sfbCoefficientQuotientTower ℤ_[ℓ]
        (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ⋙ sfbPointConstantRing :=
  (sfb_completed_coefficients.{u} ℓ).2.1.choose
```

## New

```lean
@[irreducible] noncomputable def purZlPointReduction (ℓ : ℕ) [Fact ℓ.Prime] :
    (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ℓ])) ⟶
      sfbCoefficientQuotientTower ℤ_[ℓ]
        (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ])) ⋙ sfbPointConstantRing :=
  (pur_normalized_reduction_cone.{u} ℓ).choose
```

## Users

`tools/downstream.py Sheaf.Paper.CondensedZlReduction --uses purZlPointReduction`
finds uses only inside the item. Its `purZlReduction` consumer is updated in the
same module through the unchanged public definition, and the proof establishes
its normalization and unchanged quotient theorem. No external source consumer
needs adaptation. The following is the complete transitive import-consumer list.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedZlReduction | W3 | Internal consumer checked by the full module compile. |
| Sheaf.Paper.CondensedTateRealization | D5 | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.DiagonalTowerCoefficients | U4 | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Paper.RationalTatePullback | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | No use of `purZlPointReduction`; signatures and proofs unchanged. |

## Status

landed 20261024T191541-L-426386 2026-10-24 (merge of deliver/W3/Sheaf.Paper.CondensedZlReduction)
