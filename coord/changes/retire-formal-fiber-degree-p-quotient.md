# MvPowerSeries.FormalFiberDegreePQuotient

## Reason

Retirement item from `coord/retire-items.tsv`, authorized by the human's hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The official twin proves the exact same theorem
under `MvPowerSeries.nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct`. A textual comparison
of the entire declaration confirms that only its name differs. Retire the redundant Sheaf
module and redirect its node to the official declaration.

## Old

Module: `Sheaf.RingTheory.FormalFiberDegreePQuotient`.

```lean
theorem FormalFiberDegreePQuotient
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L)
    (F : Type u) [CommRing F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] (z : L)
    (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    Nonempty ((Polynomial (TensorProduct K M F) ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C
        (Algebra.TensorProduct.includeLeftRingHom a)} :
          Set (Polynomial (TensorProduct K M F)))) ≃+* TensorProduct K L F)
```

## New

Module: `WeilConjectures.RingTheory.FormalFiberDegreePQuotient`.
The Sheaf module is withdrawn using `deleted.txt`; it adds no replacement declaration.
The node's Lean attachment uses the existing official theorem:

```lean
theorem nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L)
    (F : Type u) [CommRing F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] (z : L)
    (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    Nonempty ((Polynomial (TensorProduct K M F) ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C
        (Algebra.TensorProduct.includeLeftRingHom a)} :
          Set (Polynomial (TensorProduct K M F)))) ≃+* TensorProduct K L F)
```

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation | unmodified | Already imports the official twin and calls the official theorem; compiles unchanged. |

The retirement inventory's former consumer
`Sheaf.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation` is already absent.
Repository-wide Lean searches find no import of the retired module and no use of its old
name outside its own declaration. The only DAG attachment is
`new-lem-weil-pbc-degree-p-quotient-component`; it is redirected in this delivery.
There are no consumer adaptations. No definition or target statement changes.

## Status

landed 20261020T135415-L-1820138 2026-10-20 (merge of deliver/M1/Sheaf.RingTheory.FormalFiberDegreePQuotient)
