/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.PrimeFieldFiltration
import WeilConjectures.AlgebraicGeometry.Curve.PrimeCoefficientConstructibilityTransfer
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Constructible sheaves over finite rings have finite prime-field filtrations

Source: Stacks Project, Theorem 03SC, second proof paragraph; Lemma 03RZ.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Every constructible sheaf over a finite ring lies in the finite extension
closure of constructible sheaves with prime-field underlying abelian sheaves.
Source: Stacks Project, Theorem 03SC, second proof paragraph; Lemma 03RZ. -/
theorem constructible_hasPrimeFieldFiltration
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    HasPrimeFieldFiltration Λ X F := by
  have prime_case (r : ℕ) (hr : r.Prime)
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [IsConstructibleSheaf G] (hG : r • 𝟙 G = 0) : HasPrimeFieldFiltration Λ X G := by
    let : Fact r.Prime := ⟨hr⟩
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    have hUG : r • 𝟙 (U.obj G) = 0 := by
      ext V x
      have h := congrArg (fun f : G ⟶ G ↦ f.hom.app V x) hG
      exact h
    obtain ⟨H, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X r (U.obj G) hUG
    let := isConstructibleSheaf_prime_of_underlyingAbelianIso Λ X r G H e
    exact HasPrimeFieldFiltration.prime r G H e
  have induction_step (n : ℕ) : 0 < n →
      ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsConstructibleSheaf G → n • 𝟙 G = 0 → HasPrimeFieldFiltration Λ X G := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn G hG hkill
      let := hG
      by_cases hone : n = 1
      · have hid : 𝟙 G = 0 := by simpa [hone] using hkill
        exact prime_case 2 Nat.prime_two G (by rw [hid, smul_zero])
      · obtain ⟨p, hp, m, hpm⟩ := Nat.exists_prime_and_dvd hone
        have hm : 0 < m := by
          by_contra h
          have : m = 0 := Nat.eq_zero_of_not_pos h
          simp [this] at hpm
          omega
        have hmn : m < n := by
          rw [hpm]
          exact lt_mul_of_one_lt_left hm hp.one_lt
        let φ : G ⟶ G := p • 𝟙 G
        let K := Limits.kernel φ
        let Q := Limits.cokernel (Limits.kernel.ι φ)
        let S := ShortComplex.mk (Limits.kernel.ι φ) (Limits.cokernel.π (Limits.kernel.ι φ))
          (Limits.cokernel.condition (Limits.kernel.ι φ))
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Limits.kernel.ι φ) }
        let : IsConstructibleSheaf K := IsConstructibleSheaf.kernel φ
        let : IsConstructibleSheaf Q := IsConstructibleSheaf.cokernel (Limits.kernel.ι φ)
        have hK : p • 𝟙 K = 0 := by
          apply (cancel_mono (Limits.kernel.ι φ)).mp
          simpa [K, φ, Preadditive.nsmul_comp, Preadditive.comp_nsmul] using
            Limits.kernel.condition φ
        have hQ : m • 𝟙 Q = 0 := by
          have hcomp : (m • 𝟙 G) ≫ φ = 0 := by
            simpa [φ, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
              smul_smul, ← hpm, Nat.mul_comm] using hkill
          have h := Abelian.comp_coimage_π_eq_zero hcomp
          apply (cancel_epi (Limits.cokernel.π (Limits.kernel.ι φ))).mp
          simpa [Q, Abelian.coimage.π, Preadditive.nsmul_comp,
            Preadditive.comp_nsmul] using h
        exact HasPrimeFieldFiltration.extension S hS (prime_case p hp K hK)
          (ih m hmn hm Q inferInstance hQ)
  apply induction_step (ringChar Λ)
    (Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite Λ (ringChar Λ))) F inferInstance
  ext U x
  change ringChar Λ • x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, CharP.cast_eq_zero Λ (ringChar Λ), zero_smul]

end AlgebraicGeometry.Scheme
