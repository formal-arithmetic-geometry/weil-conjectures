/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedForgetMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunctionMate
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarCompCoherence

/-!
# The derived base change map of the condensed realization along a pushforward

Let `g : Z ⟶ Y` be a morphism of `k₀`-schemes and `ḡ : Z̄ ⟶ Ȳ` its base change to the geometric
fibres. The mate `Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*` of the pullback comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso` is the right derived
comparison of the underived pushforward comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationLowerStarIso`
(`AlgebraicGeometry.ProEtaleWeilSheaf.mateEquiv_derivedCondensedRealizationUpperStarIso`), and as
`N = forget ⋙ Φ`, it is the derived comparison
`CategoryTheory.Endofunctor.IsoAlgebra.derivedForgetCommIso` of forgetting the Weil structure
followed by the derived comparison of the condensed model with the pushforwards
(`AlgebraicGeometry.ProEtaleWeilSheaf.mateEquiv_derivedCondensedRealizationUpperStarIso_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor TwoSquare

namespace CategoryTheory.Functor

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The isomorphism of derived categories induced by the inverse of a square of exact functors is
the inverse of the induced isomorphism. -/
lemma mapDerivedCategorySquareIso_symm_inv (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (mapDerivedCategorySquareIso e.symm).inv = (mapDerivedCategorySquareIso e).hom := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Iso.symm_hom]
  rw [← mapDerivedCategoryNatIso_symm e.symm, Iso.symm_symm_eq, Category.assoc]

end CategoryTheory.Functor

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom)

/-- The base change map of the forgetful functors along the lifted adjunction
`mapOfNatIsoAdjunction adj eL eR h` and `adj` is the identification
`mapOfNatIso eR ⋙ forget F ≅ forget G ⋙ R`. -/
lemma mateEquiv_mapOfNatIsoCompForgetIso_inv :
    mateEquiv (mapOfNatIsoAdjunction adj eL eR h) adj (mapOfNatIsoCompForgetIso eL).inv =
      TwoSquare.mk _ _ _ _ (mapOfNatIsoCompForgetIso eR).hom :=
  TwoSquare.ext _ _ fun M ↦ (mateEquiv_mapOfNatIsoCompForgetIso_inv_app adj eL eR h M).trans rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The condensed realization commutes with pushforward: `g_* ⋙ N_Y ≅ N_Z ⋙ ḡ_*`, the
(invertible) mate of `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationUpperStarIso`. -/
noncomputable def condensedRealizationLowerStarIso :
    lowerStar k₀ l g ⋙ condensedRealization k₀ l Y ≅
      condensedRealization k₀ l Z ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
  asIso (mateEquiv (upperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (condensedRealizationUpperStarIso k₀ l g).hom).natTrans
/-- `AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationLowerStarIso` is the pasting of the
identification of the pushforwards of pro-étale Weil sheaves and of `ℓ`-adic sheaves along the
forgetful functors (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso`) with the
comparison of the pushforwards in the two models of `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso`). -/
lemma condensedRealizationLowerStarIso_hom :
    (condensedRealizationLowerStarIso k₀ l g).hom =
      (TwoSquare.mk (lowerStar k₀ l g) (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
        (adicLowerStar l (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
        (IsoAlgebra.mapOfNatIsoCompForgetIso
          (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).hom ≫ᵥ
      TwoSquare.mk (adicLowerStar l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
        (adicSheafEquivCondensedMod l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor
        (adicSheafEquivCondensedMod l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
        (adicLowerStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).hom).natTrans := by
  have h := mateEquiv_vcomp (upperStarLowerStarAdjunction k₀ l g)
    (adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (IsoAlgebra.mapOfNatIsoCompForgetIso
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).inv
    (adicUpperStarCompCondensedModIso l
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv
  have h₂ : mateEquiv (upperStarLowerStarAdjunction k₀ l g)
      (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (IsoAlgebra.mapOfNatIsoCompForgetIso
        (adicUpperStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).inv =
      TwoSquare.mk _ _ _ _ (IsoAlgebra.mapOfNatIsoCompForgetIso
        (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).hom := by
    exact IsoAlgebra.mateEquiv_mapOfNatIsoCompForgetIso_inv
      (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))
      (mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l g _)
  have h₁ : mateEquiv (adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).inv =
      TwoSquare.mk _ _ _ _ (adicLowerStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).hom :=
    mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom _
  rw [condensedRealizationLowerStarIso, asIso_hom]
  exact (congrArg TwoSquare.natTrans h).trans (by rw [h₂, h₁])
/-- **The derived base change map of the condensed realization along a pushforward.** The mate
`Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*` of
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso` is the right derived
comparison of the underived pushforward comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationLowerStarIso`
(`CategoryTheory.Adjunction.derived_exact_forget_mate`). -/
lemma mateEquiv_derivedCondensedRealizationUpperStarIso :
    (mateEquiv (derivedUpperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans =
      (Functor.rightDerivedFunctorCommIso (condensedRealizationLowerStarIso k₀ l g)).hom := by
  refine (Adjunction.mateEquiv_derivedAdjunction_leftDerivedFunctorSquareIso
    (upperStarLowerStarAdjunction k₀ l g)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (condensedRealizationUpperStarIso k₀ l g)).trans ?_
  rw [← Functor.mapDerivedCategorySquareIso_symm_inv]
  exact Adjunction.derived_exact_forget_mate (upperStarLowerStarAdjunction k₀ l g)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (condensedRealization k₀ l Y) (condensedRealization k₀ l Z)
    (condensedRealizationUpperStarIso k₀ l g).symm (condensedRealizationLowerStarIso k₀ l g) rfl
set_option maxHeartbeats 1000000 in
/-- **The derived base change map of the condensed realization along a pushforward, through
the two factors of the condensed realization.** As `N = forget ⋙ Φ`, the derived base change map
`Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*` is the comparison of forgetting the Weil structure with the
derived pushforwards (`CategoryTheory.Endofunctor.IsoAlgebra.derivedForgetCommIso`) followed by
the comparison of the condensed model `Φ` with the derived pushforwards, up to the identifications
`D(forget ⋙ Φ) ≅ D(forget) ⋙ D(Φ)`. -/
lemma mateEquiv_derivedCondensedRealizationUpperStarIso_app
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) :
    (mateEquiv (derivedUpperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans.app K =
      (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
          (adicSheafEquivCondensedMod l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).hom.app
          ((lowerStar k₀ l g).rightDerivedFunctor.obj K) ≫
        (adicSheafEquivCondensedMod l
          (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory.map
          ((IsoAlgebra.derivedForgetCommIso.{u + 1, u + 1, u + 2, u + 2}
            (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))).hom.app K) ≫
        (Functor.rightDerivedFunctorCommIso (adicLowerStarCompCondensedModIso l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))).hom.app
          ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategory.obj K) ≫
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso
            (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
            (adicSheafEquivCondensedMod l
              (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).inv.app K) := by
  letI := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  letI := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have hd : IsoAlgebra.derivedForgetCommIso.{u + 1, u + 1, u + 2, u + 2}
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _)) =
      Functor.rightDerivedFunctorCommIso (IsoAlgebra.mapOfNatIsoCompForgetIso
        (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _)) :
          lowerStar k₀ l g ⋙ IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y) ≅
            IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙
              adicLowerStar l (Scheme.Hom.geometricFiberMap g (comp_over g _))) :=
    rfl
  have hY : Functor.mapDerivedCategoryNatIso (Iso.refl (condensedRealization k₀ l Y) :
      IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y) ⋙
        (adicSheafEquivCondensedMod l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor ≅
          condensedRealization k₀ l Y) = Iso.refl _ :=
    Iso.ext Functor.mapDerivedCategoryNatIso_refl
  have hZ : Functor.mapDerivedCategoryNatIso (Iso.refl (condensedRealization k₀ l Z) :
      IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙
        (adicSheafEquivCondensedMod l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor ≅
          condensedRealization k₀ l Z) = Iso.refl _ :=
    Iso.ext Functor.mapDerivedCategoryNatIso_refl
  rw [mateEquiv_derivedCondensedRealizationUpperStarIso,
    Functor.rightDerivedFunctorCommIso_hom_app_comp
      (adicLowerStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
      (IsoAlgebra.mapOfNatIsoCompForgetIso
        (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _)) :
          lowerStar k₀ l g ⋙ IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y) ≅
            IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙
              adicLowerStar l (Scheme.Hom.geometricFiberMap g (comp_over g _)))
      (condensedRealizationLowerStarIso k₀ l g)
      (Iso.refl (condensedRealization k₀ l Z) :
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙
          (adicSheafEquivCondensedMod l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor ≅
            condensedRealization k₀ l Z)
      (Iso.refl (condensedRealization k₀ l Y) :
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y) ⋙
          (adicSheafEquivCondensedMod l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor ≅
            condensedRealization k₀ l Y) ?_ K, hY, hZ, hd]
  · simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.refl_inv,
      Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · intro K
    rw [condensedRealizationLowerStarIso_hom]
    simp only [TwoSquare.vComp, IsoAlgebra.mapOfNatIsoCompForgetIso, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
      Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtaleWeilSheaf
