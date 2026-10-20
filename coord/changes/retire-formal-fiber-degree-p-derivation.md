# MvPowerSeries.FormalFiberDegreePDerivation

## Reason

This module is a `retire` item in `coord/retire-items.tsv`. The official upstream
module already proves the same theorem under the declaration
`MvPowerSeries.exists_derivation_isUnit_tmul_formalFiber`; the complete signatures
are identical except for the declaration name. The duplicate Sheaf module is
withdrawn and its DAG node is redirected to the upstream declaration.

## Old

Module: `Sheaf.RingTheory.FormalFiberDegreePDerivation`.

```lean
theorem FormalFiberDegreePDerivation
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime]
    (L : Type u) [Field L]
    [Algebra ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    (M : IntermediateField
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L)
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    (z : L) (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    ∃ D : Derivation ℤ R R, IsUnit (D (Algebra.TensorProduct.includeLeftRingHom a))
```

## New

The Sheaf module is withdrawn through `deleted.txt`. Its existing DAG node now
attaches to `WeilConjectures.RingTheory.FormalFiberDegreePDerivation`:

```lean
theorem exists_derivation_isUnit_tmul_formalFiber
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ)
    (q : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) [q.IsPrime]
    (L : Type u) [Field L]
    [Algebra ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L]
    (M : IntermediateField
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) L)
    [Module.Finite
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    [IsPurelyInseparable
      ((⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).ResidueField) M]
    (z : L) (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    let A := MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
    let K := (⊥ : Ideal A).ResidueField
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := TensorProduct K M ((⊥ : Ideal A).Fiber C)
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    ∃ D : Derivation ℤ R R, IsUnit (D (Algebra.TensorProduct.includeLeftRingHom a))
```

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation | unmodified | Already imports the official upstream module and calls the official theorem; compiles unchanged. |

No Lean module imports the retired Sheaf module, and no module uses the old declaration
outside its own file. The existing DAG node is retained and redirected. No target or
definition changes.

## Status

landed 20261020T221246-L-4164808 2026-10-20 (merge of deliver/M2/Sheaf.RingTheory.FormalFiberDegreePDerivation)
