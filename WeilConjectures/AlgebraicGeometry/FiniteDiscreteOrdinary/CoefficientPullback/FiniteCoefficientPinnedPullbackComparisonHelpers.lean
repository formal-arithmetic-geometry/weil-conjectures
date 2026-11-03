/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullback
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
import all WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullbackComposition
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-! Transport identities for inverse mates and single-complex squares.

(blueprint: lem-pur-pinned-mate-single-transport).

For inverseMate_leftUniq, apply the composite adjunction hom-equivalence to leftAdjointUniq and
use its unit formula; identify the result with conjugation and apply the iterated-mate identity.
For inverseMate_transport, eliminate the two functor equalities, cancel identity whiskerings,
substitute the equality of direct-image squares, and apply injectivity of mateEquiv. For
single_square, cancel the exact composition comparison and use its single-complex formula and
the natural-iso single-complex formula. For single_square_transport, expand the whiskered
comparisons, move the edge isomorphism through the two single-complex arrows by naturality,
cancel inverse factors, apply single_square, and move the other vertex isomorphism by
naturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

-- Step 1: identify the inverse mate with the canonical left-adjoint uniqueness map.
/-- Source: categorical transport calculation for the pinned comparison.
(blueprint: lem-pur-pinned-mate-single-transport). -/
theorem inverseMate_leftUniq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (G : C ≌ E) (H : D ≌ F)
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G.functor ≅ H.functor ⋙ R₂) :
    ((mateEquiv a₁ a₂).symm β.hom).natTrans =
      ((G.toAdjunction.comp a₂).leftAdjointUniq
        ((a₁.comp H.toAdjunction).ofNatIsoRight
          (Iso.inverseCompIso (G := H)
            (Iso.isoCompInverse (H := G) β ≪≫ Functor.associator _ _ _)))).hom := by
  let α := (mateEquiv a₁ a₂).symm β.hom
  let b := a₁.comp H.toAdjunction
  let a := G.toAdjunction.comp a₂
  let k := Iso.isoCompInverse (H := G) β ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := H) k
  have eq : (a.leftAdjointUniq (b.ofNatIsoRight kr)).hom =
      (conjugateEquiv b a).symm kr.hom := by
    ext M
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    exact unit_conjugateEquiv_symm b a kr.hom M
  change α.natTrans = (a.leftAdjointUniq (b.ofNatIsoRight kr)).hom
  rw [eq]
  apply (conjugateEquiv b a).injective
  rw [Equiv.apply_symm_apply]
  rw [← iterated_mateEquiv_conjugateEquiv a₁ a₂ G.toAdjunction H.toAdjunction α]
  dsimp only [α]
  rw [Equiv.apply_symm_apply]
  ext M
  simp [kr, k, mateEquiv, Iso.inverseCompIso, Iso.isoCompInverse]

/-- Source: categorical transport calculation for the pinned comparison.
(blueprint: lem-pur-pinned-mate-single-transport). -/
theorem inverseMate_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H H' : D ⥤ F} (hG : G = G') (hH : H = H')
    (α : L₁ ⋙ H ≅ G ⋙ L₂) (β : R₁ ⋙ G ≅ H ⋙ R₂)
    (β' : R₁ ⋙ G' ≅ H' ⋙ R₂)
    (hb : isoWhiskerLeft R₁ (eqToIso hG).symm ≪≫ β ≪≫
      isoWhiskerRight (eqToIso hH) R₂ = β')
    (hm : mateEquiv a₁ a₂ α.inv = β.hom) :
    (isoWhiskerLeft L₁ (eqToIso hH).symm ≪≫ α ≪≫
      isoWhiskerRight (eqToIso hG) L₂).symm.hom =
        ((mateEquiv a₁ a₂).symm β'.hom).natTrans := by
  subst G' H'
  simp only [eqToIso_refl, Iso.refl_symm, isoWhiskerLeft_refl,
    isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl] at hb ⊢
  subst β'
  apply congrArg TwoSquare.natTrans
  have hh : (α.inv : TwoSquare G L₁ L₂ H) = (mateEquiv a₁ a₂).symm β.hom := by
    simpa only [Equiv.symm_apply_apply] using congrArg (mateEquiv a₁ a₂).symm hm
  exact hh


-- Step 8: the localized square on a single complex is the original heart square.
/-- Source: categorical transport calculation for the pinned comparison.
(blueprint: lem-pur-pinned-mate-single-transport). -/
theorem single_square
    {C D H V : Type*} [Category C] [Category D] [Category H] [Category V]
    [Abelian C] [Abelian D] [Abelian H] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    [HasDerivedCategory V]
    (F : C ⥤ D) (G : D ⥤ V) (J : C ⥤ H) (I : H ⥤ V)
    [F.Additive] [G.Additive] [J.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ J ⋙ I) (M : C) :
    (mapDerivedCategorySquareIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        I.mapDerivedCategory.map ((J.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (I.mapDerivedCategorySingleFunctor 0).hom.app (J.obj M) =
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor V 0).map (e.hom.app M) := by
  apply (cancel_epi ((mapDerivedCategoryCompIso F G).hom.app
    ((DerivedCategory.singleFunctor C 0).obj M))).1
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [mapDerivedCategoryCompIso_hom_app_singleFunctor,
    mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (mapDerivedCategoryCompIso_hom_app_singleFunctor F G M)]

-- Step 8: change the four exact comparison isomorphisms using naturality.
/-- Source: categorical transport calculation for the pinned comparison.
(blueprint: lem-pur-pinned-mate-single-transport). -/
theorem single_square_transport
    {C D H V : Type*} [Category C] [Category D] [Category H] [Category V]
    [Abelian C] [Abelian D] [Abelian H] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    [HasDerivedCategory V]
    (F : C ⥤ D) (G : D ⥤ V) (J : C ⥤ H) (I : H ⥤ V)
    [F.Additive] [G.Additive] [J.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    {F' : DerivedCategory C ⥤ DerivedCategory D}
    {I' : DerivedCategory H ⥤ DerivedCategory V}
    {G' : DerivedCategory D ⥤ DerivedCategory V}
    {J' : DerivedCategory C ⥤ DerivedCategory H}
    (a : F' ≅ F.mapDerivedCategory) (b : I' ≅ I.mapDerivedCategory)
    (x : G.mapDerivedCategory ≅ G') (y : J.mapDerivedCategory ≅ J')
    (e : F ⋙ G ≅ J ⋙ I) (M : C) :
    (isoWhiskerRight a G' ≪≫ isoWhiskerLeft F.mapDerivedCategory x.symm ≪≫
      mapDerivedCategorySquareIso e ≪≫ isoWhiskerRight y I.mapDerivedCategory ≪≫
      isoWhiskerLeft J' b.symm).hom.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        I'.map (y.inv.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
          (J.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        b.hom.app ((DerivedCategory.singleFunctor H 0).obj (J.obj M)) ≫
        (I.mapDerivedCategorySingleFunctor 0).hom.app (J.obj M) =
      G'.map (a.hom.app ((DerivedCategory.singleFunctor C 0).obj M)) ≫
        G'.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        x.inv.app ((DerivedCategory.singleFunctor D 0).obj (F.obj M)) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor V 0).map (e.hom.app M) := by
  have hs := single_square F G J I e M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% b.inv.naturality (y.inv.app ((DerivedCategory.singleFunctor _ 0).obj M))]
  rw [← reassoc_of% b.inv.naturality ((J.mapDerivedCategorySingleFunctor 0).hom.app M)]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hs
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% x.inv.naturality ((F.mapDerivedCategorySingleFunctor 0).hom.app M)]

/-- The transported single-complex equation with its comparison maps kept as isomorphisms.
Source: single-complex square transport and naturality.
(blueprint: lem-pur-pinned-mate-single-transport). -/
theorem single_square_transport_iso
    {C D H V : Type*} [Category C] [Category D] [Category H] [Category V]
    [Abelian C] [Abelian D] [Abelian H] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]
    [HasDerivedCategory V]
    (F : C ⥤ D) (G : D ⥤ V) (J : C ⥤ H) (I : H ⥤ V)
    [F.Additive] [G.Additive] [J.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    {F' : DerivedCategory C ⥤ DerivedCategory D}
    {I' : DerivedCategory H ⥤ DerivedCategory V}
    {G' : DerivedCategory D ⥤ DerivedCategory V}
    {J' : DerivedCategory C ⥤ DerivedCategory H}
    (a : F' ≅ F.mapDerivedCategory) (b : I' ≅ I.mapDerivedCategory)
    (x : G.mapDerivedCategory ≅ G') (y : J.mapDerivedCategory ≅ J')
    (e : F ⋙ G ≅ J ⋙ I) (M : C) :
    (isoWhiskerRight a G' ≪≫ isoWhiskerLeft F.mapDerivedCategory x.symm ≪≫
      mapDerivedCategorySquareIso e ≪≫ isoWhiskerRight y I.mapDerivedCategory ≪≫
      isoWhiskerLeft J' b.symm).hom.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        (I'.mapIso ((isoWhiskerLeft (DerivedCategory.singleFunctor C 0) y.symm ≪≫
          J.mapDerivedCategorySingleFunctor 0).app M) ≪≫
          b.app ((DerivedCategory.singleFunctor H 0).obj (J.obj M)) ≪≫
          (I.mapDerivedCategorySingleFunctor 0).app (J.obj M)).hom =
      ((isoWhiskerRight a G').app ((DerivedCategory.singleFunctor C 0).obj M) ≪≫
        G'.mapIso ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
        (isoWhiskerLeft (DerivedCategory.singleFunctor D 0) x.symm ≪≫
          G.mapDerivedCategorySingleFunctor 0).app (F.obj M)).hom ≫
        (DerivedCategory.singleFunctor V 0).map (e.hom.app M) := by
  simpa only [Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, Functor.map_comp, Functor.comp_obj, Category.assoc] using
    single_square_transport F G J I a b x y e M

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
