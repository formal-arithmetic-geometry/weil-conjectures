/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
public import WeilConjectures.WeilSheaf.UpperStarConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarUnit

/-!
# The constant Weil sheaf as finite-base descent

The canonical unit comparison for pullback respects the Frobenius descent datum.
The coefficient equivalence and the degree-zero embedding then identify native
descent of the finite-base unit with the constant Weil complex.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- Unit pullback is compatible with the descent isomorphism of an automorphism
over the base. -/
lemma adicUpperStarUnitIso_descent {X Y : Scheme.{u}}
    (p : X ⟶ Y) (a : X ⟶ X) (h : a ≫ p = p) :
    (adicUpperStarComp l a p).inv.app (AdicSheaf.unit l Y) ≫
        (adicUpperStarCongr l h).hom.app (AdicSheaf.unit l Y) ≫
        (adicUpperStarUnitIso l p).hom =
      (a)^*ᵃ[l].map (adicUpperStarUnitIso l p).hom ≫
        (adicUpperStarUnitIso l a).hom := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom, adicUpperStar_map_hom,
    adicUpperStarUnitIso, Mod.regularIsoOfIsIso_hom_hom]
  rw [upperStarCongr_hom_app_comp_upperStarAdicConstantSheafHom,
    upperStarAdicConstantSheafHom_comp, Iso.inv_hom_id_app_assoc]

/-- Switching between pullback and inverse pushforward preserves the unit map. -/
lemma adicUpperStarIsoLowerStarInv_hom_comp_unit {X Y : Scheme.{u}} (e : X ≅ Y) :
    (adicUpperStarIsoLowerStarInv l e).hom.app (AdicSheaf.unit l Y) ≫
        (adicLowerStarUnitIso l e.symm).hom = (adicUpperStarUnitIso l e.hom).hom := by
  apply Mod.hom_ext
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicLowerStarUnitIso_hom_hom]
  exact upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom l e

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Descent of the native finite-base unit is the constant native Weil sheaf. -/
noncomputable def geometricFiberPullbackUnitIso :
    (geometricFiberPullback k₀ l X).obj (AdicSheaf.unit l X) ≅ adicConstant k₀ l X :=
  IsoAlgebra.isoMk (adicUpperStarUnitIso l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj) (by
      rw [← cancel_epi ((adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app _)]
      rw [← NatTrans.naturality_assoc]
      change _ ≫ ((adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app _ ≫
        (adicLowerStarUnitIso l
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).hom) = _
      rw [adicUpperStarIsoLowerStarInv_hom_comp_unit]
      simp only [geometricFiberPullback_obj_str, geometricFiberPullbackFrobeniusIso,
        Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id_app_assoc]
      exact (adicUpperStarUnitIso_descent _ _ _).symm)

/-- The native constant sheaf, in condensed coordinates, is descent of the unit. -/
noncomputable def toCondensedAdicConstantDescentIso :
    (toCondensed k₀ l X).obj (adicConstant k₀ l X) ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (𝟙_ _) :=
  (toCondensed k₀ l X).mapIso (geometricFiberPullbackUnitIso k₀ l X).symm ≪≫
    (geometricFiberPullbackCompToCondensedIso k₀ l X).app (AdicSheaf.unit l X) ≪≫
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapIso (adicSheafEquivCondensedModTensorUnitIso l X)

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Native descent of the finite-base tensor unit is the constant Weil complex. -/
noncomputable def finiteBaseNativeDescentUnitIso :
    (finiteBaseNativeDescent (k₀ := k₀) (l := l) (X := X)).obj (𝟙_ _) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X) :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.preimageIso
      ((finiteBaseNativeDescentComparison (k₀ := k₀) (l := l) (X := X)).app (𝟙_ _) ≪≫
        (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.mapIso
            (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
        (derivedEquivCondensedSingleIso (WeilSheaf.adicConstant k₀ l X) (𝟙_ _)
          (ProEtaleWeilSheaf.toCondensedAdicConstantDescentIso k₀ l X)).symm))

end AlgebraicGeometry.WeilComplex
