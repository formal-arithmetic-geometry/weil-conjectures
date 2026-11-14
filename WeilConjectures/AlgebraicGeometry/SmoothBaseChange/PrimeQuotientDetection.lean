/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Detecting a prime cyclic coefficient inside a nonzero ring quotient

Source: Stacks Project, Tag 03FD, with the vector-space retract argument needed in the
arbitrary-ring reading of the coefficient step in Tag 0F08.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem quotient_retract (Λ : Type (u + 1)) [CommRing Λ]
    (r : ℕ) (hr : r.Prime) (hunit : ¬ IsUnit (r : Λ)) :
    Nonempty (Retract
      (AddCommGrpCat.of ((ULift.{u + 1} (ZMod r)) ⧸
        (Ideal.span {(r : ULift.{u + 1} (ZMod r))})))
      (AddCommGrpCat.of (Λ ⧸ (Ideal.span {(r : Λ)})))) := by
  classical
  let V := Λ ⧸ (Ideal.span {(r : Λ)})
  have : Nontrivial V := Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hunit)
  have hrV : (r : V) = 0 := by
    change Ideal.Quotient.mk _ (r : Λ) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have : Fact r.Prime := ⟨hr⟩
  have : CharP V r := (CharP.charP_iff_prime_eq_zero hr).mpr hrV
  let f : ZMod r →+* V := ZMod.castHom (dvd_refl r) V
  let : Algebra (ZMod r) V := f.toAlgebra
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod r) (one_ne_zero : (1 : V) ≠ 0)
  let P := ULift.{u + 1} (ZMod r)
  have hrP : (r : P) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self r
  have hspan : Ideal.span {(r : P)} = ⊥ := by rw [hrP, Ideal.span_singleton_zero]
  let e : (P ⧸ Ideal.span {(r : P)}) ≃+* ZMod r :=
    (Ideal.quotEquivOfEq hspan).trans ((RingEquiv.quotientBot P).trans ULift.ringEquiv)
  refine ⟨⟨AddCommGrpCat.ofHom (f.toAddMonoidHom.comp e.toAddMonoidHom),
    AddCommGrpCat.ofHom (e.symm.toAddMonoidHom.comp φ.toAddMonoidHom), ?_⟩⟩
  ext x
  change e.symm (φ (f (e x))) = x
  have hf (a : ZMod r) : φ (f a) = a := by
    have ha : f a = a • (1 : V) := by
      simp only [Algebra.smul_def, mul_one]
      rfl
    rw [ha, map_smul, hφ, smul_eq_mul, mul_one]
  rw [hf, e.symm_apply_apply]

private theorem preservesSheafification_forget_modules
    (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u}) :
    Y.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  let F := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have : F.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  let e : F ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1} ≅
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} := Iso.refl _
  have : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso e
  infer_instance

/-- Vanishing for Lambda/rLambda implies vanishing for the prime cyclic coefficient
whenever r is prime and is not a unit in Lambda.

Source: Stacks Project, Tag 03FD, module/abelian cohomology comparison; Tag 0F08, proof's
coefficient reduction. -/
theorem isZero_prime_cyclic_higherDirectImage_of_quotient
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (r : ℕ) (hr : r.Prime) (hunit : ¬ IsUnit (r : Λ))
    (hzero : IsZero (higherDirectImage Λ h q (constantModSheaf Λ Y r))) :
    IsZero (higherDirectImage (ULift.{u + 1} (ZMod r)) h q
      (constantModSheaf (ULift.{u + 1} (ZMod r)) Y r)) := by
  let P := ULift.{u + 1} (ZMod r)
  let V := Λ ⧸ (Ideal.span {(r : Λ)})
  let W := P ⧸ (Ideal.span {(r : P)})
  let UΛ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let UP := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1})
  have : UΛ.PreservesZeroMorphisms := ⟨fun _ _ ↦ by rfl⟩
  have : UP.PreservesZeroMorphisms := ⟨fun _ _ ↦ by rfl⟩
  let T := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  let C := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  obtain ⟨eΛ⟩ := nonempty_higherDirectImage_forget_iso Λ h q (constantModSheaf Λ Y r)
  obtain ⟨eP⟩ := nonempty_higherDirectImage_forget_iso P h q (constantModSheaf P Y r)
  have := preservesSheafification_forget_modules Λ Y
  have := preservesSheafification_forget_modules P Y
  let cΛ := (constantCommuteCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app (ModuleCat.of Λ V)
  let cP := (constantCommuteCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1})).app (ModuleCat.of P W)
  have hV : IsZero (T.obj (C.obj (AddCommGrpCat.of V))) :=
    (UΛ.map_isZero hzero).of_iso (eΛ ≪≫ T.mapIso cΛ).symm
  obtain ⟨a⟩ := quotient_retract Λ r hr hunit
  let b := (a.map C).map T
  have hW : IsZero (T.obj (C.obj (AddCommGrpCat.of W))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← b.retract, hV.eq_of_tgt b.i 0, zero_comp]
  have hP : IsZero (UP.obj (higherDirectImage P h q (constantModSheaf P Y r))) :=
    hW.of_iso (eP ≪≫ T.mapIso cP)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply UP.zero_of_map_zero
  change UP.map (𝟙 (higherDirectImage P h q (constantModSheaf P Y r))) = 0
  rw [UP.map_id]
  exact (IsZero.iff_id_eq_zero _).mp hP

end AlgebraicGeometry.Etale
