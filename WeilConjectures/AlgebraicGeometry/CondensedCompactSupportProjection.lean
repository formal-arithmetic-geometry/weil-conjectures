/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComparisons
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.CondensedCompactSupportProjectionCore
import WeilConjectures.AlgebraicGeometry.CondensedProperOpenScalar
import WeilConjectures.AlgebraicGeometry.CondensedPushScalarComposition
import WeilConjectures.CategoryTheory.UnitNormalizedLiftComposition
import WeilConjectures.CategoryTheory.ConjugateCompositionComponents
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-! # Condensed compact-support refinement coherence

The constructions and their existing proved coherence laws are publicly imported
from the core module. The composition proof keeps the original normalized maps.
(blueprint: def-pur-condensed-compact-support-projection). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _


attribute [local instance] fieldSheafAbelian
attribute [local instance] fieldSheafColimits
attribute [local instance] fieldSheafGrothendieck
attribute [local instance] fieldSheafBigColimits
attribute [local instance] fieldSheafCoequalizers
attribute [local instance] fieldSheafMonoidalPreadditive
attribute [local instance] fieldModuleAbelian
attribute [local instance] fieldModuleGrothendieck
attribute [local instance] fieldModuleKInjectiveResolutions
attribute [local instance] fieldModuleDerivedCategory
attribute [local instance] fieldModuleColimits
attribute [local instance] fieldModuleBigColimits
attribute [local instance] fieldSheafFlatResolution
attribute [local instance] fieldModuleFlatResolution
attribute [local instance] fieldModuleCountableCoproducts
attribute [local instance] fieldModuleIntegerColimits
attribute [local instance] fieldModuleIntegerExactColimits
attribute [local instance] fieldTensorColimits
attribute [local instance] fieldTensorColimitsRight
attribute [local instance] fieldGradedTensor
attribute [local instance] fieldGradedFour
attribute [local instance] fieldGradedLeft
attribute [local instance] fieldGradedRight
attribute [local instance] fieldExtendScalarsKFlat

namespace WeilConjectures.CompactSupportCondensedRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem fieldProperOpen_spec {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫
        fieldProperOpenRestriction Λ r K.obj =
      (fieldOpenAdjunction Λ c.i).unit.app K.obj :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose_spec


attribute [local irreducible] fieldProperOpen fieldOpenAdjunction
  fieldProperOpenRestrictionNat
attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

private theorem fieldRefinement_eq_nat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    fieldRefinement Λ r = fieldRefinementNat Λ r := by
  rfl

section RefinementCompositionProof

attribute [local irreducible] fieldDerivedUpperStar fieldDerivedLowerStar
  fieldDerivedOpenShriek
  fieldDerivedPullComp fieldDerivedAdjunction
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek

attribute [local irreducible] conjugateEquiv conjugateIsoEquiv mateEquiv

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem fieldPushComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fieldPushComp Λ f g).hom =
      conjugateEquiv ((fieldDerivedAdjunction Λ g).comp (fieldDerivedAdjunction Λ f))
        (fieldDerivedAdjunction Λ (f ≫ g)) (fieldDerivedPullComp Λ f g).hom := by
  have hh := conjugateIsoEquiv_apply_hom
    ((fieldDerivedAdjunction Λ g).comp (fieldDerivedAdjunction Λ f))
    (fieldDerivedAdjunction Λ (f ≫ g)) (fieldDerivedPullComp Λ f g)
  unfold fieldPushComp
  exact hh

attribute [local irreducible] fieldPushComp

private theorem fieldPushComp_normalized
    {A B E : Scheme.{u}} (r : A ⟶ B) (g : B ⟶ E) (f : A ⟶ E)
    (hr : r ≫ g = f) :
    conjugateEquiv ((fieldDerivedAdjunction Λ g).comp (fieldDerivedAdjunction Λ r))
        (fieldDerivedAdjunction Λ f)
        (eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k) hr.symm) ≫
          (fieldDerivedPullComp Λ r g).hom) =
      (fieldPushComp Λ r g).hom ≫
        eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k) hr) := by
  subst f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (fieldPushComp_hom Λ r g).symm

private theorem fieldPushComp_normalizedIso
    {A B E : Scheme.{u}} (r : A ⟶ B) (g : B ⟶ E) (f : A ⟶ E)
    (hr : r ≫ g = f) :
    conjugateEquiv ((fieldDerivedAdjunction Λ g).comp (fieldDerivedAdjunction Λ r))
        (fieldDerivedAdjunction Λ f)
        ((eqToIso (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k) hr.symm)) ≪≫
          fieldDerivedPullComp Λ r g).hom =
      (fieldPushComp Λ r g).hom ≫
        eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k) hr) := by
  simpa only [Iso.trans_hom, eqToIso.hom] using fieldPushComp_normalized Λ r g f hr

private theorem fieldPullComp_triangle_transport
    {W A B D : Scheme.{u}} (i : W ⟶ A) (r : A ⟶ B) (s : B ⟶ D)
    (t : A ⟶ D) (j : W ⟶ B) (k : W ⟶ D)
    (hir : i ≫ r = j) (hjs : j ≫ s = k) (hit : i ≫ t = k)
    (hrt : r ≫ s = t)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D))) :
    ((eqToIso (congrArg (fun h : W ⟶ D ↦ fieldDerivedUpperStar Λ h)
        hjs.symm)) ≪≫ fieldDerivedPullComp Λ j s).hom.app N ≫
      ((eqToIso (congrArg (fun h : W ⟶ B ↦ fieldDerivedUpperStar Λ h)
        hir.symm)) ≪≫ fieldDerivedPullComp Λ i r).hom.app
          ((fieldDerivedUpperStar Λ s).obj N) =
    ((eqToIso (congrArg (fun h : W ⟶ D ↦ fieldDerivedUpperStar Λ h)
        hit.symm)) ≪≫ fieldDerivedPullComp Λ i t).hom.app N ≫
      (fieldDerivedUpperStar Λ i).map
        (((eqToIso (congrArg (fun h : A ⟶ D ↦ fieldDerivedUpperStar Λ h)
          hrt.symm)) ≪≫ fieldDerivedPullComp Λ r s).hom.app N) := by
  subst t
  cases hir
  cases hjs
  conv_lhs => simp only [eqToIso_refl, Iso.refl_trans]
  conv_rhs =>
    simp only [eqToIso_refl, Iso.refl_trans]
    rw [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, Category.assoc, eqToHom_app]
  unfold fieldDerivedPullComp fieldDerivedUpperStar
  exact CondensedRing.leftDerivedUpperStarComp_assoc_app Λ i r s N

private theorem fieldPullComp_outer_triangle
    {A B D E : Scheme.{u}} (r : A ⟶ B) (s : B ⟶ D) (h : D ⟶ E)
    (g : B ⟶ E) (f : A ⟶ E) (hs : s ≫ h = g) (hr : r ≫ g = f)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology E) Ab.{u + 1})
      (condensedRingObj Λ E))) :
    (eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k) hr.symm) ≫
        (fieldDerivedPullComp Λ r g).hom).app N ≫
      (fieldDerivedUpperStar Λ r).map
        ((eqToHom (congrArg (fun k : B ⟶ E ↦ fieldDerivedUpperStar Λ k) hs.symm) ≫
          (fieldDerivedPullComp Λ s h).hom).app N) =
    (eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k)
        (show (r ≫ s) ≫ h = f by rw [Category.assoc, hs, hr]).symm) ≫
      (fieldDerivedPullComp Λ (r ≫ s) h).hom).app N ≫
        (fieldDerivedPullComp Λ r s).hom.app ((fieldDerivedUpperStar Λ h).obj N) := by
  subst g
  subst f
  conv_lhs => simp only [NatTrans.comp_app, eqToHom_refl, Category.id_comp]
  let e := eqToIso (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k)
    (Category.assoc r s h))
  change (fieldDerivedPullComp Λ r (s ≫ h)).hom.app N ≫
      (fieldDerivedUpperStar Λ r).map ((fieldDerivedPullComp Λ s h).hom.app N) =
    (e.inv.app N ≫ (fieldDerivedPullComp Λ (r ≫ s) h).hom.app N) ≫
      (fieldDerivedPullComp Λ r s).hom.app ((fieldDerivedUpperStar Λ h).obj N)
  apply (cancel_epi (e.hom.app N)).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  dsimp only [e]
  rw [eqToIso.hom, eqToHom_app]
  unfold fieldDerivedPullComp fieldDerivedUpperStar
  exact (CondensedRing.leftDerivedUpperStarComp_assoc_app Λ r s h N).symm

private theorem conjugateComposition_whole
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {H : E ⥤ D} {G : D ⥤ E} {T : D ⥤ A} {V : A ⥤ D}
    {F : E ⥤ A} {Rf : A ⥤ E} {K : E ⥤ B} {Rk : B ⥤ E}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ah : H ⊣ G) (ac : T ⊣ V)
    (af : F ⊣ Rf) (ak : K ⊣ Rk)
    (α : F ⟶ K ⋙ P) (β : K ⟶ H ⋙ Q) (gamma : F ⟶ H ⋙ T) (τ : T ⟶ Q ⋙ P)
    (hc : ∀ N, α.app N ≫ P.map (β.app N) =
      gamma.app N ≫ τ.app (H.obj N))
    (t : R ⋙ S ⟶ V) (a : R ⋙ Rk ⟶ Rf) (b : S ⋙ G ⟶ Rk) (c : V ⋙ G ⟶ Rf)
    (ht : conjugateEquiv (aq.comp ap) ac τ = t)
    (ha : conjugateEquiv (ak.comp ap) af α = a)
    (hb : conjugateEquiv (ah.comp aq) ak β = b)
    (hg : conjugateEquiv (ah.comp ac) af gamma = c) :
    Functor.whiskerRight t G ≫ c = Functor.whiskerLeft R b ≫ a := by
  ext M
  exact CategoryTheory.conjugateComposition_app ap aq ah ac af ak α β gamma τ hc
    t a b c ht ha hb hg M

private theorem fieldPushComp_triangle
    {A B D E : Scheme.{u}} (r : A ⟶ B) (s : B ⟶ D) (h : D ⟶ E)
    (g : B ⟶ E) (f : A ⟶ E) (hs : s ≫ h = g) (hr : r ≫ g = f) :
    Functor.whiskerRight (fieldPushComp Λ r s).hom (fieldDerivedLowerStar Λ h) ≫
        ((fieldPushComp Λ (r ≫ s) h).hom ≫
          eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k)
            (show (r ≫ s) ≫ h = f by rw [Category.assoc, hs, hr]))) =
      Functor.whiskerLeft (fieldDerivedLowerStar Λ r)
        ((fieldPushComp Λ s h).hom ≫
          eqToHom (congrArg (fun k : B ⟶ E ↦ fieldDerivedLowerStar Λ k) hs)) ≫
        ((fieldPushComp Λ r g).hom ≫
          eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k) hr)) := by
  exact conjugateComposition_whole
    (fieldDerivedAdjunction Λ r) (fieldDerivedAdjunction Λ s)
    (fieldDerivedAdjunction Λ h) (fieldDerivedAdjunction Λ (r ≫ s))
    (fieldDerivedAdjunction Λ f) (fieldDerivedAdjunction Λ g)
    (eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k) hr.symm) ≫
      (fieldDerivedPullComp Λ r g).hom)
    (eqToHom (congrArg (fun k : B ⟶ E ↦ fieldDerivedUpperStar Λ k) hs.symm) ≫
      (fieldDerivedPullComp Λ s h).hom)
    (eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedUpperStar Λ k)
      (show (r ≫ s) ≫ h = f by rw [Category.assoc, hs, hr]).symm) ≫
      (fieldDerivedPullComp Λ (r ≫ s) h).hom)
    (fieldDerivedPullComp Λ r s).hom
    (fieldPullComp_outer_triangle Λ r s h g f hs hr)
    (fieldPushComp Λ r s).hom
    ((fieldPushComp Λ r g).hom ≫
      eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k) hr))
    ((fieldPushComp Λ s h).hom ≫
      eqToHom (congrArg (fun k : B ⟶ E ↦ fieldDerivedLowerStar Λ k) hs))
    ((fieldPushComp Λ (r ≫ s) h).hom ≫
      eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k)
        (show (r ≫ s) ≫ h = f by rw [Category.assoc, hs, hr])))
    (fieldPushComp_hom Λ r s).symm
    (fieldPushComp_normalized Λ r g f hr)
    (fieldPushComp_normalized Λ s h g hs)
    (fieldPushComp_normalized Λ (r ≫ s) h f
      (show (r ≫ s) ≫ h = f by rw [Category.assoc, hs, hr]))

private theorem fieldPushComp_triangle_transport
    {A B D E : Scheme.{u}} (r : A ⟶ B) (s : B ⟶ D) (t : A ⟶ D) (h : D ⟶ E)
    (g : B ⟶ E) (f : A ⟶ E) (hrt : r ≫ s = t) (hs : s ≫ h = g)
    (hr : r ≫ g = f) (ht : t ≫ h = f) :
    Functor.whiskerRight
        ((fieldPushComp Λ r s).hom ≫
          eqToHom (congrArg (fun k : A ⟶ D ↦ fieldDerivedLowerStar Λ k) hrt))
        (fieldDerivedLowerStar Λ h) ≫
      ((fieldPushComp Λ t h).hom ≫
        eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k) ht)) =
    Functor.whiskerLeft (fieldDerivedLowerStar Λ r)
      ((fieldPushComp Λ s h).hom ≫
        eqToHom (congrArg (fun k : B ⟶ E ↦ fieldDerivedLowerStar Λ k) hs)) ≫
      ((fieldPushComp Λ r g).hom ≫
        eqToHom (congrArg (fun k : A ⟶ E ↦ fieldDerivedLowerStar Λ k) hr)) := by
  cases hrt
  simp only [eqToHom_refl, Category.comp_id]
  exact fieldPushComp_triangle Λ r s h g f hs hr

private theorem unitNormalizedRestrictionLift_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {T : D ⥤ A} {V : A ⥤ D}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ac : T ⊣ V)
    (U : A ⥤ C) (U' : B ⥤ C) (U'' : D ⥤ C)
    (J : C ⥤ A) (J' : C ⥤ B) (J'' : C ⥤ D)
    (aj : J ⊣ U) (aj' : J' ⊣ U') (aj'' : J'' ⊣ U'')
    (α : U' ≅ P ⋙ U) (β : U'' ≅ Q ⋙ U') (gamma : U'' ≅ T ⋙ U)
    (τ : T ≅ Q ⋙ P)
    (hc : ∀ N, β.hom.app N ≫ α.hom.app (Q.obj N) =
      gamma.hom.app N ≫ U.map (τ.hom.app N)) (K : C)
    (Nr : U'.obj (R.obj (J.obj K)) ⟶ U.obj (J.obj K))
    (Ns : U''.obj (S.obj (J'.obj K)) ⟶ U'.obj (J'.obj K))
    (Nc : U''.obj (V.obj (J.obj K)) ⟶ U.obj (J.obj K))
    (hNr : Nr = (counitRestrictionNat J ap U U' α).app K)
    (hNs : Ns = (counitRestrictionNat J' aq U' U'' β).app K)
    (hNc : Nc = (counitRestrictionNat J ac U U'' gamma).app K)
    (u : J'.obj K ⟶ R.obj (J.obj K)) (v : J''.obj K ⟶ S.obj (J'.obj K))
    (w : J''.obj K ⟶ V.obj (J.obj K))
    (hu : aj'.homEquiv K (R.obj (J.obj K)) u ≫ Nr = aj.unit.app K)
    (hv : aj''.homEquiv K (S.obj (J'.obj K)) v ≫ Ns = aj'.unit.app K)
    (hw : aj''.homEquiv K (V.obj (J.obj K)) w ≫ Nc = aj.unit.app K)
    (hun : ∃! w' : J''.obj K ⟶ V.obj (J.obj K),
      aj''.homEquiv K (V.obj (J.obj K)) w' ≫ Nc = aj.unit.app K)
    (p : R ⋙ S ⟶ V) (hp : p = conjugateEquiv (aq.comp ap) ac τ.hom) :
    w = v ≫ S.map u ≫ p.app (J.obj K) := by
  rw [hp]
  apply CategoryTheory.unitNormalizedLift_comp ap aq ac U U' U'' J J' J'' aj aj' aj''
    α β gamma τ hc K Nr Ns Nc _ _ _ u v w hu hv hw hun
  · rw [hNr]
    rfl
  · rw [hNs]
    rfl
  · rw [hNc]
    rfl

private theorem unitNormalizedRestrictionNatLift_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {T : D ⥤ A} {V : A ⥤ D}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ac : T ⊣ V)
    (U : A ⥤ C) (U' : B ⥤ C) (U'' : D ⥤ C)
    (J : C ⥤ A) (J' : C ⥤ B) (J'' : C ⥤ D)
    (aj : J ⊣ U) (aj' : J' ⊣ U') (aj'' : J'' ⊣ U'')
    (α : U' ≅ P ⋙ U) (β : U'' ≅ Q ⋙ U') (gamma : U'' ≅ T ⋙ U)
    (τ : T ≅ Q ⋙ P)
    (hc : ∀ N, β.hom.app N ≫ α.hom.app (Q.obj N) =
      gamma.hom.app N ≫ U.map (τ.hom.app N)) (K : C)
    (Nr : U'.obj (R.obj (J.obj K)) ⟶ U.obj (J.obj K))
    (Ns : U''.obj (S.obj (J'.obj K)) ⟶ U'.obj (J'.obj K))
    (Nc : U''.obj (V.obj (J.obj K)) ⟶ U.obj (J.obj K))
    (Nrt : (J ⋙ R) ⋙ U' ⟶ J ⋙ U)
    (Nst : (J' ⋙ S) ⋙ U'' ⟶ J' ⋙ U')
    (Nct : (J ⋙ V) ⋙ U'' ⟶ J ⋙ U)
    (hNrt : Nrt = counitRestrictionNat J ap U U' α)
    (hNst : Nst = counitRestrictionNat J' aq U' U'' β)
    (hNct : Nct = counitRestrictionNat J ac U U'' gamma)
    (hNr : Nr = Nrt.app K) (hNs : Ns = Nst.app K) (hNc : Nc = Nct.app K)
    (u : J'.obj K ⟶ R.obj (J.obj K)) (v : J''.obj K ⟶ S.obj (J'.obj K))
    (w : J''.obj K ⟶ V.obj (J.obj K))
    (hu : aj'.homEquiv K (R.obj (J.obj K)) u ≫ Nr = aj.unit.app K)
    (hv : aj''.homEquiv K (S.obj (J'.obj K)) v ≫ Ns = aj'.unit.app K)
    (hw : aj''.homEquiv K (V.obj (J.obj K)) w ≫ Nc = aj.unit.app K)
    (hun : ∃! w' : J''.obj K ⟶ V.obj (J.obj K),
      aj''.homEquiv K (V.obj (J.obj K)) w' ≫ Nc = aj.unit.app K)
    (p : R ⋙ S ⟶ V) (hp : p = conjugateEquiv (aq.comp ap) ac τ.hom) :
    w = v ≫ S.map u ≫ p.app (J.obj K) := by
  apply unitNormalizedRestrictionLift_comp ap aq ac U U' U'' J J' J'' aj aj' aj''
    α β gamma τ hc K Nr Ns Nc _ _ _ u v w hu hv hw hun p hp
  · rw [hNr, hNrt]
  · rw [hNs, hNst]
  · rw [hNc, hNct]

private theorem fieldProperOpenRestrictionNat_counit
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d) :
    fieldProperOpenRestrictionNat Λ r =
      (counitRestrictionNat (fieldDerivedOpenShriek Λ c.i)
        (fieldDerivedAdjunction Λ r.hom) (fieldDerivedUpperStar Λ c.i)
        (fieldDerivedUpperStar Λ d.i)
        ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦ fieldDerivedUpperStar Λ h)
          r.i_hom.symm)) ≪≫ fieldDerivedPullComp Λ c.i r.hom)) := by
  unfold fieldProperOpenRestrictionNat
  rfl

private theorem fieldProperOpenRestriction_app
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    fieldProperOpenRestriction Λ r K = (fieldProperOpenRestrictionNat Λ r).app K := by
  exact Eq.refl (fieldProperOpenRestriction Λ r K)

attribute [local irreducible] counitRestrictionNat

private theorem fieldProperOpen_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    fieldProperOpen Λ (r.comp s) K =
      fieldProperOpen Λ s K ≫
        (fieldDerivedLowerStar Λ s.hom).map (fieldProperOpen Λ r K) ≫
          ((fieldPushComp Λ r.hom s.hom).hom ≫
            eqToHom (congrArg (fun k : c.Z ⟶ e.Z ↦ fieldDerivedLowerStar Λ k)
              (show r.hom ≫ s.hom = (r.comp s).hom from rfl))).app
                ((fieldDerivedOpenShriek Λ c.i).obj K.obj) := by
  exact unitNormalizedRestrictionNatLift_comp
    (fieldDerivedAdjunction Λ r.hom) (fieldDerivedAdjunction Λ s.hom)
    (fieldDerivedAdjunction Λ (r.comp s).hom)
    (fieldDerivedUpperStar Λ c.i) (fieldDerivedUpperStar Λ d.i)
    (fieldDerivedUpperStar Λ e.i)
    (fieldDerivedOpenShriek Λ c.i) (fieldDerivedOpenShriek Λ d.i)
    (fieldDerivedOpenShriek Λ e.i)
    (fieldOpenAdjunction Λ c.i) (fieldOpenAdjunction Λ d.i) (fieldOpenAdjunction Λ e.i)
    ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦ fieldDerivedUpperStar Λ h)
        r.i_hom.symm)) ≪≫ fieldDerivedPullComp Λ c.i r.hom)
    ((eqToIso (congrArg (fun h : X ⟶ e.Z ↦ fieldDerivedUpperStar Λ h)
        s.i_hom.symm)) ≪≫ fieldDerivedPullComp Λ d.i s.hom)
    ((eqToIso (congrArg (fun h : X ⟶ e.Z ↦ fieldDerivedUpperStar Λ h)
        (r.comp s).i_hom.symm)) ≪≫
      fieldDerivedPullComp Λ c.i (r.comp s).hom)
    ((eqToIso (congrArg (fun k : c.Z ⟶ e.Z ↦ fieldDerivedUpperStar Λ k)
      (show r.hom ≫ s.hom = (r.comp s).hom from rfl).symm)) ≪≫
        fieldDerivedPullComp Λ r.hom s.hom)
    (fieldPullComp_triangle_transport Λ c.i r.hom s.hom (r.comp s).hom d.i e.i
      r.i_hom s.i_hom (r.comp s).i_hom rfl)
    K.obj (fieldProperOpenRestriction Λ r K.obj) (fieldProperOpenRestriction Λ s K.obj)
    (fieldProperOpenRestriction Λ (r.comp s) K.obj)
    (fieldProperOpenRestrictionNat Λ r) (fieldProperOpenRestrictionNat Λ s)
    (fieldProperOpenRestrictionNat Λ (r.comp s))
    (fieldProperOpenRestrictionNat_counit Λ r)
    (fieldProperOpenRestrictionNat_counit Λ s)
    (fieldProperOpenRestrictionNat_counit Λ (r.comp s))
    (fieldProperOpenRestriction_app Λ r K.obj)
    (fieldProperOpenRestriction_app Λ s K.obj)
    (fieldProperOpenRestriction_app Λ (r.comp s) K.obj)
    (fieldProperOpen Λ r K) (fieldProperOpen Λ s K) (fieldProperOpen Λ (r.comp s) K)
    (fieldProperOpen_spec Λ r K) (fieldProperOpen_spec Λ s K)
    (fieldProperOpen_spec Λ (r.comp s) K) (fieldProperOpen_existsUnique Λ (r.comp s) K)
    ((fieldPushComp Λ r.hom s.hom).hom ≫
      eqToHom (congrArg (fun k : c.Z ⟶ e.Z ↦ fieldDerivedLowerStar Λ k)
        (show r.hom ≫ s.hom = (r.comp s).hom from rfl)))
    (fieldPushComp_normalizedIso Λ r.hom s.hom (r.comp s).hom rfl).symm

private theorem assembly_comp
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (R : A ⥤ B) (S : B ⥤ D) (V : A ⥤ D) (G : D ⥤ E)
    (H : B ⥤ E) (F : A ⥤ E)
    (t : S ⋙ G ⟶ H) (a : R ⋙ H ⟶ F) (c : V ⋙ G ⟶ F) (p : R ⋙ S ⟶ V)
    {M : A} {N : B} {O : D}
    (u : N ⟶ R.obj M) (v : O ⟶ S.obj N) (w : O ⟶ V.obj M)
    (hw : w = v ≫ S.map u ≫ p.app M)
    (hc : Functor.whiskerRight p G ≫ c = Functor.whiskerLeft R t ≫ a) :
    G.map w ≫ c.app M = (G.map v ≫ t.app N) ≫ (H.map u ≫ a.app M) := by
  rw [hw, G.map_comp, G.map_comp]
  simp only [Category.assoc]
  have hcomp := NatTrans.congr_app hc M
  change G.map (p.app M) ≫ c.app M = t.app (R.obj M) ≫ a.app M at hcomp
  rw [hcomp]
  have h := t.naturality u
  change G.map (S.map u) ≫ t.app (R.obj M) = t.app N ≫ H.map u at h
  rw [reassoc_of% h]

private theorem assembleLiftNat_comp
    {C A B D E : Type*} [Category C] [Category A] [Category B]
    [Category D] [Category E]
    (I : C ⥤ A) (J : C ⥤ B) (K : C ⥤ D)
    (R : A ⥤ B) (S : B ⥤ D) (V : A ⥤ D) (G : D ⥤ E)
    (H : B ⥤ E) (F : A ⥤ E)
    (t : S ⋙ G ⟶ H) (a : R ⋙ H ⟶ F) (c : V ⋙ G ⟶ F) (p : R ⋙ S ⟶ V)
    (u : J ⟶ I ⋙ R) (v : K ⟶ J ⋙ S) (w : K ⟶ I ⋙ V)
    (hw : ∀ N, w.app N = v.app N ≫ S.map (u.app N) ≫ p.app (I.obj N))
    (hc : Functor.whiskerRight p G ≫ c = Functor.whiskerLeft R t ≫ a) :
    assembleLiftNat K I V G F w c =
      assembleLiftNat K J S G H v t ≫ assembleLiftNat J I R H F u a := by
  ext N
  exact assembly_comp R S V G H F t a c p (u.app N) (v.app N) (w.app N) (hw N) hc

private theorem fieldRefinementNat_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    fieldRefinementNat Λ (r.comp s) =
      fieldRefinementNat Λ s ≫ fieldRefinementNat Λ r := by
  exact assembleLiftNat_comp
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ c.i)
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ d.i)
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ e.i)
    (fieldDerivedLowerStar Λ r.hom) (fieldDerivedLowerStar Λ s.hom)
    (fieldDerivedLowerStar Λ (r.comp s).hom)
    (fieldDerivedLowerStar Λ e.g) (fieldDerivedLowerStar Λ d.g)
    (fieldDerivedLowerStar Λ c.g)
    ((fieldPushComp Λ s.hom e.g).hom ≫
      eqToHom (congrArg (fun h : d.Z ⟶ Y ↦ fieldDerivedLowerStar Λ h) s.hom_g))
    ((fieldPushComp Λ r.hom d.g).hom ≫
      eqToHom (congrArg (fun h : c.Z ⟶ Y ↦ fieldDerivedLowerStar Λ h) r.hom_g))
    ((fieldPushComp Λ (r.comp s).hom e.g).hom ≫
      eqToHom (congrArg (fun h : c.Z ⟶ Y ↦ fieldDerivedLowerStar Λ h) (r.comp s).hom_g))
    ((fieldPushComp Λ r.hom s.hom).hom ≫
      eqToHom (congrArg (fun h : c.Z ⟶ e.Z ↦ fieldDerivedLowerStar Λ h)
        (show r.hom ≫ s.hom = (r.comp s).hom from rfl)))
    (fieldProperOpenNat Λ r) (fieldProperOpenNat Λ s) (fieldProperOpenNat Λ (r.comp s))
    (fieldProperOpen_comp Λ r s)
    (fieldPushComp_triangle_transport Λ r.hom s.hom (r.comp s).hom
      e.g d.g c.g rfl s.hom_g r.hom_g (r.comp s).hom_g)

end RefinementCompositionProof

/-- The field and closure refinements have the same composition normalization.
Source: blueprint proof Steps 15--16; Stacks 0F7B and 07A7
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two iterated maps under the open adjunction. Proper counit
pasting identifies their common transpose with the composite-refinement unit.
Uniqueness gives equality; the proper-image mate compositor is associative. -/
theorem fieldRefinement_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    fieldRefinement Λ (r.comp s) = fieldRefinement Λ s ≫ fieldRefinement Λ r := by
  rw [fieldRefinement_eq_nat Λ (r.comp s), fieldRefinement_eq_nat Λ s,
    fieldRefinement_eq_nat Λ r]
  exact fieldRefinementNat_comp Λ r s


end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [FlatCoefficientMap a]

/-- Coefficient extension commutes with the original refinement map itself.
Source: blueprint proof Steps 15--16; proper/open coefficient mate pasting
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two composites under the open adjunction. Coefficient restriction
commutes with the original open unit and the proper counit, so both transposes are
the same section-normalized restriction map. Uniqueness in the open Hom bijection
and the proper compositor identify the original maps. This applies verbatim to the
finite-valued closure coefficient and requires no new choice of comparison arrow. -/
theorem condensedProjection_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (condensedScalar a Y).map ((fieldRefinement Λ r).app K) ≫
        (condensedProjection a c).app K.obj =
      (condensedProjection a d).app K.obj ≫
        (fieldRefinement Λ' r).app ⟨(condensedScalar a X).obj K.obj, hK⟩ := by
  have hproper := condensedPushScalar_refinement_factorization a r K
  have hopen := fieldProperOpen_scalar_pasting a r K hK
  calc
    _ = _ := hproper
    _ = _ := hopen

end WeilConjectures.CompactSupportCondensedRealization


attribute [instance 2000] fieldSheafColimits
  fieldSheafGrothendieck
  fieldSheafBigColimits
  fieldSheafCoequalizers
  fieldSheafMonoidalPreadditive
  fieldModuleGrothendieck
  fieldModuleKInjectiveResolutions
  fieldModuleColimits
  fieldModuleBigColimits
  fieldSheafFlatResolution
  fieldModuleFlatResolution

attribute [instance 2000] fieldModuleCountableCoproducts fieldModuleIntegerColimits
  fieldModuleIntegerExactColimits fieldExtendScalarsKFlat

attribute [instance 2000] fieldSheafAbelian fieldModuleAbelian fieldModuleDerivedCategory
