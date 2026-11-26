/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.PopescuSpecialChartPolynomial
import WeilConjectures.RingTheory.PopescuZeroBaseChartPolynomial

/-! # Smooth fibres of the prepared Popescu quotient on a chart

On each prepared chart of the Popescu lifting algebra, the special fibre and the residue-field
fibre are smooth.

## Implementation details

No annihilator hypothesis is needed for this calculation modulo `π`.

## References

* [Stacks, Tag 07CP] (computation modulo `π` on a chart and the coefficient calculation
  comparing the different charts)
-/

@[expose] public section

universe a c

namespace Algebra

/-- The special fibre and the residue-field fibre are smooth on each prepared chart. -/
theorem popescu_lift_chart_fibres (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
      (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (hcmod : cmod.comp (Ideal.Quotient.mk _) = c.toRingHom)
    (q : PrimeSpectrum (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (k : Fin d.r) (hk : c (d.ε (d.reduced (d.a k))) ∉ q.asIdeal) :
    let qD := PrimeSpectrum.comap (Ideal.Quotient.mk _) q
    let p := PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD
    IsSmoothAtPrime p.asIdeal.ResidueField
      (PrimeSpectrum.preimageEquivFiber R d.liftingAlgebra p ⟨qD, rfl⟩) ∧
    @Smooth (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) _
      (Localization.Away (c (d.ε (d.reduced (d.a k))))) _
      (letI := cmod.toAlgebra; inferInstance) := by
  classical
  let D := d.liftingAlgebra
  let J := Ideal.span ({algebraMap R D π} : Set D)
  let qD := PrimeSpectrum.comap (Ideal.Quotient.mk J) q
  let p := PrimeSpectrum.comap (algebraMap R D) qD
  let B := p.asIdeal.ResidueField
  have hπp : π ∈ p.asIdeal := by
    change Ideal.Quotient.mk J (algebraMap R D π) ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
    exact q.asIdeal.zero_mem
  have hπ : algebraMap R B π = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hπp
  let R₂ := R ⧸ Ideal.span ({π ^ 2} : Set R)
  let base : R₂ →ₐ[R] B := Ideal.Quotient.liftₐ _ (Algebra.ofId R B) (by
    change Ideal.span ({π ^ 2} : Set R) ≤ RingHom.ker (algebraMap R B)
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change algebraMap R B (π ^ 2) = 0
    rw [map_pow, hπ, zero_pow (by decide)])
  let : Algebra R₂ B := base.toRingHom.toAlgebra
  have : IsScalarTower R R₂ B := IsScalarTower.of_algHom base
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (c (d.ε (d.reduced (d.a k))))
  have hsnot : s ∉ qD.asIdeal := by
    change Ideal.Quotient.mk J s ∉ q.asIdeal
    rwa [hs]
  let t := Algebra.TensorProduct.includeRight (R := R) (A := B) s
  have ht : t ∉ (PrimeSpectrum.preimageEquivFiber R D p ⟨qD, rfl⟩).asIdeal := by
    have he := (PrimeSpectrum.preimageEquivFiber R D p).symm_apply_apply ⟨qD, rfl⟩
    have he' := congrArg (fun x ↦ x.1.asIdeal) he
    change Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
      (PrimeSpectrum.preimageEquivFiber R D p ⟨qD, rfl⟩).asIdeal = qD.asIdeal at he'
    intro h
    exact hsnot (he' ▸ h)
  obtain ⟨e⟩ := popescu_zero_base_chart_polynomial R Cbar π d hd c hc B hπ k s hs
  have : Smooth R₂ (Localization.Away (d.reducedElement k)) := hd.smooth k
  have : Smooth B (TensorProduct R₂ B (Localization.Away (d.reducedElement k))) := inferInstance
  have : Smooth (TensorProduct R₂ B (Localization.Away (d.reducedElement k)))
      (MvPolynomial (d.E k) (TensorProduct R₂ B (Localization.Away (d.reducedElement k)))) :=
    ⟨inferInstance, inferInstance⟩
  have : Smooth B
      (MvPolynomial (d.E k) (TensorProduct R₂ B (Localization.Away (d.reducedElement k)))) :=
    Smooth.comp B (TensorProduct R₂ B (Localization.Away (d.reducedElement k))) _
  have hf : Smooth B (Localization.Away t) := Smooth.of_equiv e
  refine ⟨⟨t, ht, hf⟩, ?_⟩
  let C₀ := Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)
  let := cmod.toAlgebra
  obtain ⟨e₀⟩ := popescu_special_chart_polynomial R Cbar π d hd c cmod hc hcmod k
  let a₀ : C₀ := Ideal.Quotient.mk _ (d.ε (d.reduced (d.a k)))
  have : Smooth C₀ (Localization.Away a₀) := Smooth.of_isLocalization_Away a₀
  have : Smooth (Localization.Away a₀) (MvPolynomial (d.E k) (Localization.Away a₀)) :=
    ⟨inferInstance, inferInstance⟩
  have : Smooth C₀ (MvPolynomial (d.E k) (Localization.Away a₀)) :=
    Smooth.comp C₀ (Localization.Away a₀) _
  exact Smooth.of_equiv e₀

end Algebra
