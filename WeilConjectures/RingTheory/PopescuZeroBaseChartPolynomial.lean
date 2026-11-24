/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.RingTheory.PopescuZeroBaseSingleChartPolynomial
import WeilConjectures.RingTheory.PopescuZeroBaseChartRelations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Polynomial model of a prepared lifting chart

After a scalar extension killing `π`, a chart of the lifting algebra of a prepared Popescu
lift presentation is a polynomial algebra over the scalar extension of the localized reduced
coefficient quotient.

## References

* [Stacks Project, Tag 07CP](https://stacks.math.columbia.edu/tag/07CP)
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra

private theorem localized_surjection_bijective
    {S A T : Type*} [CommRing S] [CommRing A] [CommRing T]
    [Algebra S A] [Algebra S T] (f : A →ₐ[S] T) (t : A)
    (hf : Function.Surjective f)
    (hker : ∀ x, f x = 0 → algebraMap A (Localization.Away t) x = 0) :
    Function.Bijective (IsLocalization.Away.mapₐ
      (Localization.Away t) (Localization.Away (f t)) f t) := by
  constructor
  · change Function.Injective (IsLocalization.Away.map
      (Localization.Away t) (Localization.Away (f t)) f.toRingHom t)
    apply (IsLocalization.Away.map_injective_iff (Localization.Away (f t)) f.toRingHom t).mpr
    intro x hx
    obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers t) (Localization.Away t) x).mp (hker x hx)
    obtain ⟨n, hn⟩ := u.property
    exact ⟨n, by simpa only [← hn] using hu⟩
  · exact IsLocalization.Away.mapₐ_surjective_of_surjective t hf

/-- Let `d` be a prepared Popescu lift presentation with lifting algebra `D`, let `B` be an
`R/(π²)`-algebra in which `π` vanishes, and let `s ∈ D` reduce modulo `π` to the image of
the `k`-th chart element `aₖ`. Then the localization of `B ⊗[R] D` at `1 ⊗ s` is isomorphic,
as a `B`-algebra, to the polynomial algebra on `Eₖ` over `B ⊗[R/(π²)]` the localization of
the reduced quotient at `aₖ`. -/
theorem popescu_zero_base_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) (s : d.liftingAlgebra)
    (hs : Ideal.Quotient.mk _ s = c (d.ε (d.reduced (d.a k)))) :
    Nonempty (MvPolynomial (d.E k)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
        Localization.Away (d.reducedElement k)) ≃ₐ[B]
      Localization.Away
        (Algebra.TensorProduct.includeRight (R := R) (A := B) s)) := by
  classical
  let Rbar := R ⧸ Ideal.span ({π ^ 2} : Set R)
  let D0 := d.liftingAlgebra ⧸
    Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)
  let aD : d.liftingAlgebra :=
    ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k)))
  let left : MvPolynomial (Fin d.n) R →ₐ[R] D0 :=
    c.comp ((d.ε.restrictScalars R).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId R Rbar)))
  let right : MvPolynomial (Fin d.n) R →ₐ[R] D0 :=
    (Ideal.Quotient.mkₐ R _).comp ((ULift.algEquiv (R := R)).symm.toAlgHom.comp
      ((Ideal.Quotient.mkₐ R d.definingIdeal).comp d.includeX))
  have hpoly : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    change c (d.ε (MvPolynomial.map (algebraMap R Rbar) (MvPolynomial.X i))) =
      Ideal.Quotient.mk _
        (ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (MvPolynomial.X i))))
    rw [MvPolynomial.map_X]
    simpa only [PopescuLiftPresentation.includeX, MvPolynomial.rename_X,
      PopescuLiftPresentation.x] using hc i
  have haD : c (d.ε (d.reduced (d.a k))) = Ideal.Quotient.mk _ aD :=
    DFunLike.congr_fun hpoly (d.a k)
  have hsub : s - aD ∈
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra) :=
    Ideal.Quotient.eq.mp (hs.trans haD)
  let inc := Algebra.TensorProduct.includeRight (R := R) (A := B)
    (B := d.liftingAlgebra)
  have hπT : inc (algebraMap R d.liftingAlgebra π) = 0 := by
    rw [inc.commutes, IsScalarTower.algebraMap_apply R B (B ⊗[R] d.liftingAlgebra),
      hπ, map_zero]
  have hst : inc s = inc aD := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hsub
    rw [hz, map_mul, hπT, zero_mul]
  change Nonempty (_ ≃ₐ[B] Localization.Away (inc s))
  rw [hst]
  let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
  let Dk := ULift.{c} (d.polynomial ⧸ J)
  have hJ : J ≤ d.definingIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl j => exact Ideal.subset_span ⟨.inl j, rfl⟩
    | inr l => exact Ideal.subset_span ⟨.inr (k, l), rfl⟩
  let φ : Dk →ₐ[R] d.liftingAlgebra :=
    (ULift.algEquiv (R := R)).symm.toAlgHom.comp
      ((Ideal.Quotient.liftₐ J (Ideal.Quotient.mkₐ R d.definingIdeal)
        (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hx))).comp
          (ULift.algEquiv (R := R)).toAlgHom)
  let A := B ⊗[R] Dk
  let t : A := Algebra.TensorProduct.includeRight (R := R) (A := B)
    (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k))))
  let f : A →ₐ[B] B ⊗[R] d.liftingAlgebra :=
    Algebra.TensorProduct.map (AlgHom.id B B) φ
  have hchartSurj : Function.Surjective φ := by
    rintro ⟨q⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨ULift.up (Ideal.Quotient.mk J p), rfl⟩
  have hf : Function.Surjective f :=
    Algebra.TensorProduct.map_surjective (AlgHom.id B B) φ
      Function.surjective_id hchartSurj
  let ev : d.polynomial →+* Localization.Away t :=
    (algebraMap A (Localization.Away t)).comp
      ((Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom.comp
        ((ULift.algEquiv (R := R)).symm.toRingHom.comp
          (Ideal.Quotient.mk J)))
  have hI : d.definingIdeal ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl j =>
      have hj : Ideal.Quotient.mk J (d.equation (.inl j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨Sum.inl j, rfl⟩)
      change algebraMap A (Localization.Away t)
        (Algebra.TensorProduct.includeRight (R := R) (A := B)
          (ULift.up (Ideal.Quotient.mk J (d.equation (.inl j))))) = 0
      rw [hj]
      change algebraMap A (Localization.Away t)
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (0 : Dk)) = 0
      rw [map_zero, map_zero]
    | inr kl =>
      exact d.zero_base_chart_relations R Cbar π hd B hπ k kl.1 kl.2
  have hker : ∀ x, f x = 0 → algebraMap A (Localization.Away t) x = 0 := by
    have hmap : RingHom.ker f =
        (RingHom.ker φ).map
          (Algebra.TensorProduct.includeRight (R := R) (A := B)) := by
      exact Algebra.TensorProduct.lTensor_ker (A := B) φ hchartSurj
    have hle : RingHom.ker f ≤ RingHom.ker (algebraMap A (Localization.Away t)) := by
      rw [hmap, Ideal.map_le_iff_le_comap]
      rintro ⟨q⟩ hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      have hp : p ∈ d.definingIdeal :=
        Ideal.Quotient.eq_zero_iff_mem.mp (congrArg ULift.down hq)
      exact hI hp
    exact fun x hx ↦ hle hx
  obtain ⟨e⟩ := d.zero_base_single_chart_polynomial R Cbar π
    hd.normalized_h B hπ k
  let e' := AlgEquiv.ofBijective
    (IsLocalization.Away.mapₐ (Localization.Away t) (Localization.Away (f t)) f t)
    (localized_surjection_bijective f t hf hker)
  exact ⟨e.trans e'⟩

end Algebra
