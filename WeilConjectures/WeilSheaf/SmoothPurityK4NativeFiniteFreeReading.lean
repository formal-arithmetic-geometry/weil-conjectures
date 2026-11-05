/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteFreeSitePullback

/-! # The finite free-module reading comparison respects pullback -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.K4Native

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The existing free-module site reading is compatible with the actual finite
coefficient pullback comparison and the canonical geometric pullbacks. -/
lemma purity_comparisonUpperStarFreeIso_pullback
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((CondensedRing.freeFunctorCompUpperStarIso
            (Profinite.integersModPowRingObj ℓ E n) g).hom.app (ν^*(Y)[Ab.{u + 1}].obj M)) ≫
        (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).map
            ((comparisonUpperStarUpperStarIso Ab.{u + 1} g).hom.app M)) ≫
        (comparisonUpperStarFreeIso ℓ E n X).hom.app ((Etale.upperStar Ab.{u + 1} g).obj M) =
      (upperStarFiniteCoefficientModEquivalenceIso ℓ E n g).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y)).obj
            (ν^*(Y)[Ab.{u + 1}].obj M)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((comparisonUpperStarFreeIso ℓ E n Y).hom.app M) ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
          ((Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) Y).obj M) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((Etale.upperStarExtendScalarsIso (integersModPowCoeff.{u} ℓ E n) g).hom.app M) := by
  rw [purity_comparisonUpperStarFreeIso_hom_app,
    purity_comparisonUpperStarFreeIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (purityFiniteCoefficientFreeIso ℓ E n X).hom.naturality
    ((comparisonUpperStarUpperStarIso Ab.{u + 1} g).hom.app M)
  dsimp +instances only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (purity_upperStarFiniteCoefficient_free ℓ E n g (ν^*(Y)[Ab.{u + 1}].obj M))]
  have h := purity_comparisonFreeSheaf_pullback_forward ℓ E n g M
  simp only [purityComparisonFreePullbackIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  rw [← h]

end AlgebraicGeometry.ProEtale.K4Native
