/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreePullbackCube
public import WeilConjectures.TateTwist.FiniteRootsOfUnity
public import WeilConjectures.TateTwist.TateModuleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EquivalenceCompCoherence

/-! # Finite coefficient comparison on free modules and pullback -/

set_option profiler true
set_option profiler.threshold 1

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.K4Native

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ)

/-- The finite model equivalence, with the consumer's coefficient spelling. -/
noncomputable def finiteCoefficientModEquivalence (X : Scheme.{u}) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) ≌
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) :=
  (Mod.comapEquivalenceOfIsIso
    (constRingSheafToCondensedRingObj X (PadicAlgCl.integersModPow ℓ E n))).trans
    (Sheaf.modConstRingSheafEquivalence _ (integersModPowCoeff.{u} ℓ E n))

lemma finiteCoefficientModEquivalence_functor_comp_sheafCompose (X : Scheme.{u}) :
    (finiteCoefficientModEquivalence ℓ E n X).functor ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Ab.{u + 1}) =
      Mod.forget (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

noncomputable def lowerStarFiniteCoefficientModEquivalenceIso :
    CondensedRing.lowerStar (Profinite.integersModPowRingObj ℓ E n) f ⋙
        (finiteCoefficientModEquivalence ℓ E n Y).functor ≅
      (finiteCoefficientModEquivalence ℓ E n X).functor ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f :=
  Sheaf.natIsoMkOfSheafCompose
    (F₁ := CondensedRing.lowerStar (Profinite.integersModPowRingObj ℓ E n) f ⋙
      (finiteCoefficientModEquivalence ℓ E n Y).functor)
    (F₂ := (finiteCoefficientModEquivalence ℓ E n X).functor ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f) (fun M ↦ Iso.refl _)
    (fun M U r y ↦ by
      obtain ⟨t⟩ := r
      have h1 := finiteCoefficientModEquivalence_smul Y (PadicAlgCl.integersModPow ℓ E n)
        ((CondensedRing.lowerStar (Profinite.integersModPowRingObj ℓ E n) f).obj M) U t y
      rw [globalSmul_lowerStar_obj, ProEtale.lowerStar_map_hom_app] at h1
      have h2 := finiteCoefficientModEquivalence_smul X (PadicAlgCl.integersModPow ℓ E n) M
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop)) t
      exact h1.trans (h2 y).symm)
    fun φ ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl

/-- **The comparison of the two finite-coefficient models commutes with pullback**:
`f^* ⋙ Φ_X ≅ Φ_Y ⋙ f^*`, the conjugate of `lowerStarFiniteCoefficientModEquivalenceIso`. -/
noncomputable def upperStarFiniteCoefficientModEquivalenceIso :
    CondensedRing.upperStar (Profinite.integersModPowRingObj ℓ E n) f ⋙
        (finiteCoefficientModEquivalence ℓ E n X).functor ≅
      (finiteCoefficientModEquivalence ℓ E n Y).functor ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f :=
  ((conjugateIsoEquiv
    ((CondensedRing.upperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n) f).comp
      (finiteCoefficientModEquivalence ℓ E n X).toAdjunction)
    ((finiteCoefficientModEquivalence ℓ E n Y).toAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f))).symm
    (Iso.inverseCompIso (Iso.isoCompInverse (lowerStarFiniteCoefficientModEquivalenceIso ℓ E n f) ≪≫
      Functor.associator _ _ _))).symm

variable (X : Scheme.{u})

noncomputable def finiteCoefficientModEquivalenceInverseCompForgetIso :
    (finiteCoefficientModEquivalence ℓ E n X).inverse ⋙
        Mod.forget (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Ab.{u + 1}) :=
  Functor.isoWhiskerLeft _
      (eqToIso (finiteCoefficientModEquivalence_functor_comp_sheafCompose ℓ E n X).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteCoefficientModEquivalence ℓ E n X).counitIso _ ≪≫
    Functor.leftUnitor _


end AlgebraicGeometry.ProEtale.K4Native
