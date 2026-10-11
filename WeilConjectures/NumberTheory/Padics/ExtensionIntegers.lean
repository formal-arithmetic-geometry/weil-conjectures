/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Valuation.LocalSubring
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# Rings of integers of finite extensions inside `ℚ̄_ℓ`

For finite extensions `E ⊆ L` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the ring of integers `𝒪_L` is the integral
closure of `𝒪_E` in `L` (`PadicAlgCl.isIntegralClosure_integers`), hence a finite free
`𝒪_E`-module (`PadicAlgCl.finite_integers`, `PadicAlgCl.free_integers`).

An element of `ℚ̄_ℓ` of norm at most one is integral over `ℤ_ℓ`
(`PadicAlgCl.isIntegral_integers_of_norm_le_one`): the norm of `ℚ̄_ℓ` is the spectral norm, so
the coefficients of the minimal polynomial over `ℚ_ℓ` have norm at most one.
-/

@[expose] public section

open Polynomial

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type*) [Field E] [Field L] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [Algebra L (PadicAlgCl l)]

/-- The subring of `ℚ_ℓ` mapped into `𝒪_E`. -/
noncomputable abbrev padicIntegers : Subring ℚ_[l] :=
  (integers l E).toSubring.comap (algebraMap ℚ_[l] E)

/-- The ring morphism from `padicIntegers` to `𝒪_E`. -/
noncomputable def padicIntegersMap : padicIntegers l E →+* integers l E :=
  ((algebraMap ℚ_[l] E).restrict (padicIntegers l E) (integers l E).toSubring
    fun _ hx ↦ hx)

lemma norm_le_one_mem_padicIntegers {c : ℚ_[l]} (hc : ‖c‖ ≤ 1) : c ∈ padicIntegers l E := by
  change algebraMap ℚ_[l] E c ∈ integers l E
  rw [mem_integers_iff, ← IsScalarTower.algebraMap_apply, ← NNReal.coe_le_coe, coe_nnnorm,
    NNReal.coe_one, PadicAlgCl.norm_extends]
  exact hc

/-- An element of `L` whose image in `ℚ̄_ℓ` has norm at most one is integral over `𝒪_E`, for any
morphism `E → L` over `ℚ̄_ℓ`. -/
theorem isIntegral_integers_of_norm_le_one (ι : E →+* L)
    (hι : ∀ x, algebraMap L (PadicAlgCl l) (ι x) = algebraMap E (PadicAlgCl l) x) (x : L)
    (hx : ‖algebraMap L (PadicAlgCl l) x‖ ≤ 1) :
    (ι.comp (integers l E).subtype).IsIntegralElem x := by
  set y := algebraMap L (PadicAlgCl l) x
  set p := minpoly ℚ_[l] y
  have hmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have hcoeff : ∀ n, ‖p.coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hmonic).mp hx
  have hsub : (↑p.coeffs : Set ℚ_[l]) ⊆ padicIntegers l E := fun c hc ↦ by
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    exact norm_le_one_mem_padicIntegers l E (hcoeff n)
  refine ⟨(p.toSubring _ hsub).map (padicIntegersMap l E),
    (monic_toSubring p _ hsub |>.mpr hmonic).map _, ?_⟩
  apply (algebraMap L (PadicAlgCl l)).injective
  rw [map_zero, hom_eval₂, eval₂_map]
  have : ((algebraMap L (PadicAlgCl l)).comp (ι.comp (integers l E).subtype)).comp
      (padicIntegersMap l E) =
        (algebraMap ℚ_[l] (PadicAlgCl l)).comp (padicIntegers l E).subtype := by
    ext c
    simp only [RingHom.comp_apply, Subring.subtype_apply, hι]
    exact (IsScalarTower.algebraMap_apply ℚ_[l] E (PadicAlgCl l) c).symm
  rw [this, ← eval₂_map, map_toSubring, ← aeval_def, minpoly.aeval]

end PadicAlgCl

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type*) [Field E] [Field L] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [Algebra L (PadicAlgCl l)] [Algebra E L] [IsScalarTower E L (PadicAlgCl l)]

/-- The ring morphism `𝒪_E → 𝒪_L` restricted from `E → L`, as an algebra structure. -/
noncomputable abbrev integersAlgebra : Algebra (integers l E) (integers l L) :=
  ((algebraMap E L).comp (integers l E).subtype |>.codRestrict (integers l L).toSubring
    fun x ↦ by
      change ‖algebraMap L (PadicAlgCl l) (algebraMap E L x)‖₊ ≤ 1
      rw [← IsScalarTower.algebraMap_apply]
      exact x.2).toAlgebra

/-- The algebra structure `𝒪_E → L`. -/
noncomputable abbrev integersFieldAlgebra : Algebra (integers l E) L :=
  ((algebraMap E L).comp (integers l E).subtype).toAlgebra

attribute [local instance] integersAlgebra integersFieldAlgebra

instance : IsScalarTower (integers l E) E L := .of_algebraMap_eq fun _ ↦ rfl

instance : IsScalarTower (integers l E) (integers l L) L := .of_algebraMap_eq fun _ ↦ rfl

/-- The ring of integers `𝒪_L` is the integral closure of `𝒪_E` in `L`. -/
theorem isIntegralClosure_integers :
    IsIntegralClosure (integers l L) (integers l E) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hx' : IsIntegral (integers l L) x := hx.tower_top
      obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx'
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      have h := isIntegral_integers_of_norm_le_one l E L (algebraMap E L)
        (fun x ↦ (IsScalarTower.algebraMap_apply E L (PadicAlgCl l) x).symm) y
        (by
          have : ‖algebraMap L (PadicAlgCl l) y‖₊ ≤ 1 := y.2
          exact_mod_cast this)
      exact h

variable [FiniteDimensional E L]

/-- The ring of integers `𝒪_L` of a finite extension `L ⊇ E` inside `ℚ̄_ℓ` is a finite
`𝒪_E`-module. -/
theorem finite_integers [FiniteDimensional ℚ_[l] E] :
    Module.Finite (integers l E) (integers l L) := by
  have := isIntegralClosure_integers l E L
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  exact IsIntegralClosure.finite (integers l E) E L (integers l L)

/-- The ring of integers `𝒪_L` of a finite extension `L ⊇ E` inside `ℚ̄_ℓ` is a free
`𝒪_E`-module. -/
theorem free_integers [FiniteDimensional ℚ_[l] E] :
    Module.Free (integers l E) (integers l L) := by
  have := isIntegralClosure_integers l E L
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have : Module.IsTorsionFree (integers l E) L := .trans_faithfulSMul (integers l E) E L
  exact IsIntegralClosure.module_free (integers l E) E L (integers l L)

end PadicAlgCl

open TensorProduct in
/-- If `B` is a free `A`-algebra, then `B ⧸ I B` is a free `A ⧸ I`-module: it is the base change
`(A ⧸ I) ⊗[A] B`. -/
theorem Module.free_quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] (I : Ideal A) : Module.Free (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  let e₀ : (A ⧸ I) ⊗[A] B ≃ₗ[A] B ⧸ I.map (algebraMap A B) :=
    TensorProduct.comm A (A ⧸ I) B ≪≫ₗ
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.restrictScalars A
  let e : (A ⧸ I) ⊗[A] B ≃ₗ[A ⧸ I] B ⧸ I.map (algebraMap A B) :=
    { e₀.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        have h1 : (Ideal.Quotient.mk I c) • x = c • x := algebraMap_smul (A ⧸ I) c x
        have h2 : ∀ z : B ⧸ I.map (algebraMap A B), (Ideal.Quotient.mk I c) • z = c • z :=
          fun z ↦ algebraMap_smul (A ⧸ I) c z
        change e₀ _ = _
        rw [h1, map_smul, RingHom.id_apply, h2]
        rfl }
  exact .of_basis ((Algebra.TensorProduct.basis (A ⧸ I) (Module.Free.chooseBasis A B)).map e)

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E L : Type*) [Field E] [Field L] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [Algebra L (PadicAlgCl l)] [Algebra E L] [IsScalarTower E L (PadicAlgCl l)]
  [FiniteDimensional E L] [FiniteDimensional ℚ_[l] E]

attribute [local instance] integersAlgebra

/-- The finite coefficient ring `𝒪_L ⧸ 𝔪_Eⁿ 𝒪_L` is free over `𝒪_E ⧸ 𝔪_Eⁿ`: the finite-level
statement "`B` is finite free over `A`" of blueprint `lem-coef-finite-free-extension`. -/
theorem free_quotient_integers (n : ℕ) :
    Module.Free (integers l E ⧸ IsLocalRing.maximalIdeal (integers l E) ^ n)
      (integers l L ⧸ (IsLocalRing.maximalIdeal (integers l E) ^ n).map
        (algebraMap (integers l E) (integers l L))) :=
  have := free_integers l E L
  Module.free_quotient_map _

end PadicAlgCl
