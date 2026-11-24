/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective

import WeilConjectures.Algebra.Homology.UniversalConnectiveProjectiveModel
import WeilConjectures.Algebra.Homology.AbelianVariety.ConnectiveUniversalH0ZeroDifferential
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Global normalization of a universally rank-one projective complex

A bounded finite projective complex with universally connective rank-one homology has a global
projective model starting in degree zero with zero differential out of degree zero.

## References

* Stacks Project, Tags 00O0, 0BCD and 0BF2 (projective affine adaptation)
-/

@[expose] public section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded finite projective complex with universally connective rank-one
homology has a global projective model starting in degree zero with d-zero zero.
The output terms are exhibited as retracts of finite free modules. -/
theorem universalH0_projective_normalization
    (R : Type v) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hbase : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      (∀ i : ℤ, i < 0 → IsZero (PB.homology i)) ∧
        Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ Q : CochainComplex (ModuleCat.{v} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n)) ∧
      (∀ n : ℤ, ∃ m : ℕ,
        ∃ (ι : Q.X n ⟶ ModuleCat.of R (ULift.{v} (Fin m) →₀ R))
          (π : ModuleCat.of R (ULift.{v} (Fin m) →₀ R) ⟶ Q.X n),
          ι ≫ π = 𝟙 (Q.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (Q.X n)) ∧ Q.d 0 1 = 0 ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) := by
  classical
  obtain ⟨C, hCb, hCf, hCp, hCneg, ⟨ePC⟩⟩ :=
    universalConnective_projective_model R P hb hf hp
      (fun B _ φ ↦ (hbase B φ).1)
  have hCzero (B : Type v) [CommRing B] (φ : R →+* B) :
      Nonempty
        ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj C).homology 0 ≅
          ModuleCat.of B B) := by
    have : (ModuleCat.extendScalars φ).Additive :=
      (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
    let e := (ModuleCat.extendScalars φ).mapHomotopyEquiv ePC
    exact ⟨(e.toHomologyIso 0).symm ≪≫ (hbase B φ).2.some⟩
  obtain ⟨Q, hQb, hQf, hQp, hQneg, hQd, ⟨eCQ⟩⟩ :=
    connective_universalH0_zero_differential R C hCb hCf hCp hCneg hCzero
  refine ⟨Q, hQb, ?_, hQneg, hQd, ?_⟩
  · intro n
    let := hQf n
    let := hQp n
    obtain ⟨m, π, ι, _, _, hιπ⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R (Q.X n)
    let e : (ULift.{v} (Fin m) →₀ R) ≃ₗ[R] (Fin m → R) :=
      (Finsupp.linearEquivFunOnFinite R R _).trans
        (LinearEquiv.piCongrLeft R (fun _ ↦ R) Equiv.ulift)
    refine ⟨m, ModuleCat.ofHom (e.symm.toLinearMap.comp ι),
      ModuleCat.ofHom (π.comp e.toLinearMap), ?_⟩
    ext x
    change π (e (e.symm (ι x))) = x
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.id_apply]
      using LinearMap.congr_fun hιπ x
  · let e := ePC.trans eCQ
    exact ⟨asIso (DerivedCategory.Q.map e.hom)⟩

end CochainComplex
