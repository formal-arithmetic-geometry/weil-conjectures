/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteComparison
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

/-- Extension of scalars from abelian sheaves on the pro-étale site. -/
noncomputable def purityFiniteFreeSheaf (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) :=
  Sheaf.composeAndSheafify (ProEt.topology X)
    (ModuleCat.extendScalarsAddCommGrp (integersModPowCoeff.{u} ℓ E n))

/-- The free/forget adjunction on the pro-étale site. -/
noncomputable def purityFiniteFreeSheafAdjunction (X : Scheme.{u}) :
    purityFiniteFreeSheaf ℓ E n X ⊣
      sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Ab.{u + 1}) :=
  Sheaf.adjunction _ (ModuleCat.extendScalarsAddCommGrpAdj (integersModPowCoeff.{u} ℓ E n))

/-- The finite coefficient equivalence carries free module objects to free sheaves. -/
noncomputable def purityFiniteCoefficientFreeIso (X : Scheme.{u}) :
    Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) ⋙
        (finiteCoefficientModEquivalence ℓ E n X).functor ≅ purityFiniteFreeSheaf ℓ E n X :=
  (conjugateIsoEquiv (purityFiniteFreeSheafAdjunction ℓ E n X)
    ((Mod.freeForgetAdjunction _).comp (finiteCoefficientModEquivalence ℓ E n X).toAdjunction)).symm
    (finiteCoefficientModEquivalenceInverseCompForgetIso ℓ E n X).symm

/-- Free sheaves commute with geometric pullback by the canonical mate of the
identity on the underlying direct-image abelian sheaves. -/
noncomputable def purityFiniteFreeSheafPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    purityFiniteFreeSheaf ℓ E n Y ⋙ (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)] ≅
      (g)^*[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf ℓ E n X :=
  (conjugateIsoEquiv ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
    (purityFiniteFreeSheafAdjunction ℓ E n X))
    ((purityFiniteFreeSheafAdjunction ℓ E n Y).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g))).symm
    (Iso.refl _)

lemma purity_finiteCoefficientInverseForget_inv_app (X : Scheme.{u})
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :
    (finiteCoefficientModEquivalenceInverseCompForgetIso ℓ E n X).inv.app N =
      (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Ab.{u + 1})).map
          ((finiteCoefficientModEquivalence ℓ E n X).counitInv.app N) := by
  simp [finiteCoefficientModEquivalenceInverseCompForgetIso]

lemma purity_finiteCoefficient_forget_map (X : Scheme.{u})
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)} (a : M ⟶ N) :
    (Mod.forget (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).map a =
      (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Ab.{u + 1})).map
          ((finiteCoefficientModEquivalence ℓ E n X).functor.map a) := rfl

lemma purity_lowerStarFiniteCoefficient_forget_inv {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Ab.{u + 1})).map
        ((lowerStarFiniteCoefficientModEquivalenceIso ℓ E n g).inv.app M) = 𝟙 _ := rfl

/-- Compatibility of the inverse-equivalence forget comparison with pushforward. -/
lemma purity_finiteCoefficient_free_right_square {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :
    (g)_*[Ab.{u + 1}].map
        ((finiteCoefficientModEquivalenceInverseCompForgetIso ℓ E n X).inv.app N) =
      (finiteCoefficientModEquivalenceInverseCompForgetIso ℓ E n Y).inv.app
          ((g)_*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj N) ≫
        (Mod.forget (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y)).map
          ((Iso.inverseCompIso (Iso.isoCompInverse (lowerStarFiniteCoefficientModEquivalenceIso ℓ E n g)
            ≪≫ Functor.associator _ _ _)).inv.app N) := by
  rw [purity_finiteCoefficientInverseForget_inv_app,
    purity_finiteCoefficientInverseForget_inv_app, purity_finiteCoefficient_forget_map,
    Adjunction.functor_map_inverseCompIso_isoCompInverse_inv_app]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp_assoc]
  erw [Equivalence.counitIso_inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp,
    purity_lowerStarFiniteCoefficient_forget_inv]
  erw [Category.comp_id]
  rfl

/-- The actual finite coefficient pullback comparison respects the free-module
comparisons. This is the coefficient-reading part of the finite Tate line square. -/
lemma purity_upperStarFiniteCoefficient_free {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Sheaf (ProEt.topology Y) Ab.{u + 1}) :
    (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((CondensedRing.freeFunctorCompUpperStarIso
            (Profinite.integersModPowRingObj ℓ E n) g).hom.app M) ≫
        (purityFiniteCoefficientFreeIso ℓ E n X).hom.app ((g)^*[Ab.{u + 1}].obj M) =
      (upperStarFiniteCoefficientModEquivalenceIso ℓ E n g).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y)).obj M) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((purityFiniteCoefficientFreeIso ℓ E n Y).hom.app M) ≫
        (purityFiniteFreeSheafPullbackIso ℓ E n g).hom.app M := by
  apply purity_free_pullback_cube
    (upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Mod.freeForgetAdjunction _) (Mod.freeForgetAdjunction _)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n) g)
    (finiteCoefficientModEquivalence ℓ E n Y).toAdjunction
    (finiteCoefficientModEquivalence ℓ E n X).toAdjunction
    (purityFiniteFreeSheafAdjunction ℓ E n Y) (purityFiniteFreeSheafAdjunction ℓ E n X)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g)
  intro N
  simp only [purityFiniteCoefficientFreeIso, purityFiniteFreeSheafPullbackIso,
    CondensedRing.freeFunctorCompUpperStarIso, upperStarFiniteCoefficientModEquivalenceIso,
    Adjunction.symm_conjugateIsoEquiv_symm_apply, Equiv.apply_symm_apply,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Iso.symm_hom]
  simpa only [Functor.comp_obj, Category.comp_id] using
    purity_finiteCoefficient_free_right_square ℓ E n g N

end AlgebraicGeometry.ProEtale.K4Native
