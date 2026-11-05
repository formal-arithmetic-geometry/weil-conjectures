/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteFreeReading
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteRootReading
public import WeilConjectures.WeilSheaf.SmoothPurityComparisonRestriction

/-! # Geometric compatibility of the finite free-root comparison -/

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
  (n : ℕ) (N : ℕ) (hN : 0 < N) (hT : (N : (PadicAlgCl.integersModPow ℓ E n)) = 0)
  {X Y : Scheme.{u}} (g : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
  (hX : IsUnit (N : Γ(X, ⊤)))

noncomputable def finiteCoefficientModEquivalenceFreeRootsOfUnityIso
    (Z : Scheme.{u}) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (finiteCoefficientModEquivalence Z (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Z)).obj
          (rootsOfUnitySheaf Z N)) ≅
      ν^*(Z)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        ((Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) Z).obj (Z.rootsOfUnitySheaf N)) :=
  (finiteCoefficientModEquivalence Z (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
      ((Mod.freeFunctor _).mapIso (comparisonUpperStarRootsOfUnityIso Z N hN hZ).symm) ≪≫
    (comparisonUpperStarFreeIso ℓ E n Z).app (Z.rootsOfUnitySheaf N)


include hT

/-- Inverse-coordinate form of the root comparison square. -/
lemma purity_comparisonUpperStarRootsOfUnityIso_pullback_inv :
    upperStarRootsOfUnitySheafHom g N ≫
        (comparisonUpperStarRootsOfUnityIso X N hN hX).inv =
      (g)^*[Ab.{u + 1}].map (comparisonUpperStarRootsOfUnityIso Y N hN hY).inv ≫
        (comparisonUpperStarUpperStarIso Ab.{u + 1} g).hom.app (Y.rootsOfUnitySheaf N) ≫
        ν^*(X)[Ab.{u + 1}].map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g) := by
  have hNT : (N : integersModPowCoeff.{u} ℓ E n) = 0 := by
    apply ULift.ext
    exact hT
  have h := purity_comparisonUpperStarRootsOfUnityIso_pullback
    (integersModPowCoeff.{u} ℓ E n) N hN hNT g hY hX
  rw [purity_comparisonCoefficientPullbackIso_eq, Iso.symm_inv] at h
  apply (cancel_epi ((g)^*[Ab.{u + 1}].map
    (comparisonUpperStarRootsOfUnityIso Y N hN hY).hom)).mp
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Functor.map_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The finite reading of the free module on roots of unity carries its actual
geometric datum to the canonical étale root datum. -/
lemma purity_finiteCoefficientModEquivalenceFreeRootsOfUnityIso_pullback :
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((CondensedRing.freeFunctorCompUpperStarIso
            (Profinite.integersModPowRingObj ℓ E n) g).hom.app (rootsOfUnitySheaf Y N)) ≫
        (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).map
            (upperStarRootsOfUnitySheafHom g N)) ≫
        (finiteCoefficientModEquivalenceFreeRootsOfUnityIso ℓ E n N hN X hX).hom =
      (upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n)).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y)).obj
            (rootsOfUnitySheaf Y N)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (finiteCoefficientModEquivalenceFreeRootsOfUnityIso ℓ E n N hN Y hY).hom ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
          ((Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) Y).obj (Y.rootsOfUnitySheaf N)) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((Etale.upperStarExtendScalarsIso (integersModPowCoeff.{u} ℓ E n) g).hom.app
              (Y.rootsOfUnitySheaf N) ≫
            (Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) X).map
              (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g)) := by
  have hroot := purity_comparisonUpperStarRootsOfUnityIso_pullback_inv ℓ E n N hN hT g hY hX
  have hfree := (CondensedRing.freeFunctorCompUpperStarIso
    (Profinite.integersModPowRingObj ℓ E n) g).hom.naturality
    (comparisonUpperStarRootsOfUnityIso Y N hN hY).inv
  have hread := (comparisonUpperStarFreeIso ℓ E n X).hom.naturality
    (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g)
  have hcoeff := (upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n)).hom.naturality
    ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y)).map
      (comparisonUpperStarRootsOfUnityIso Y N hN hY).inv)
  dsimp +instances only [Functor.comp_map, Functor.comp_obj] at hfree hread hcoeff
  simp only [finiteCoefficientModEquivalenceFreeRootsOfUnityIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  conv_lhs =>
    rhs; rw [← Functor.map_comp_assoc, ← Functor.map_comp, hroot]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hfree, Functor.map_comp, Category.assoc]
  rw [hread]
  rw [reassoc_of% (purity_comparisonUpperStarFreeIso_pullback ℓ E n g
    (Y.rootsOfUnitySheaf N))]
  rw [reassoc_of% hcoeff]

end AlgebraicGeometry.ProEtale.K4Native
