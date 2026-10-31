/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

/-! # Scalar-compatible open base change for condensed coefficients

Source: blueprint main-20261015, det-sf-open-closed-sequence-ring-sheaf, proof (4),
and sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp; exact localization uses
Stacks Project, Tag 04VG, lemma-properties-left-localization.
(blueprint: lem-sfb-condensed-open-square-scalar-comparison)

The pullback square comparison and its complex-level map are real constructions from
existing module pullbacks, their specified compositors, and termwise application.
The theorem retains the specified open adjunctions and ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] ProEtale.upperStarCompIso ProEtale.upperStarCongr
attribute [local irreducible] ProEtale.upperStarFromPointComp

/-- The fixed module comparison `p^* i^* ≅ j^* r^*` for `U = W ×_X Y`, using the
specified pullback compositors and the equality of the two maps `U ⟶ X`.
Source: blueprint det-sf-open-closed-sequence-ring-sheaf, proof (4), with the
module compositor of sk-def-sfb-module-pushforward-pullback.
(blueprint: lem-sfb-condensed-open-square-scalar-comparison). -/
@[irreducible]
def openSquareModulePullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W Y X : Scheme.{u}}
    (r : W ⟶ X) (i : Y ⟶ X) :
    upperStar Λ i ⋙ upperStar Λ (pullback.snd r i) ≅
      upperStar Λ r ⋙ upperStar Λ (pullback.fst r i) :=
  (upperStarComp Λ (pullback.snd r i) i).symm ≪≫
    eqToIso (congrArg (upperStar Λ) (pullback.condition (f := r) (g := i)).symm) ≪≫
      upperStarComp Λ (pullback.fst r i) r

/-- The degreewise open comparison on complexes, including the canonical termwise
composition identifications. Its degree-`n` map is `β` at the degree-`n` object.
Source: blueprint det-sf-open-closed-sequence-ring-sheaf, proof (4), exact descent
by Stacks Tag 04VG.
(blueprint: lem-sfb-condensed-open-square-scalar-comparison). -/
def openSquareComplexComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W Y X : Scheme.{u}}
    (r : W ⟶ X) (i : Y ⟶ X) [IsOpenImmersion i]
    (β : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
      upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i))
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (openImmersionLowerShriek Λ i ⋙ upperStar Λ r))
      (ComplexShape.up ℤ)).hom.app K ≫
    (NatTrans.mapHomologicalComplex β.hom (ComplexShape.up ℤ)).app K ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar Λ (pullback.snd r i) ⋙
        openImmersionLowerShriek Λ (pullback.fst r i)))
      (ComplexShape.up ℤ)).inv.app K

private theorem squareOfEssImage
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    (F : C ⥤ A) (G : A ⥤ C) (R : A ⥤ D) (P : C ⥤ B)
    (J : B ⥤ D) (H : D ⥤ B) (a : F ⊣ G) (b : J ⊣ H)
    [F.Full] [F.Faithful] [J.Full] [J.Faithful]
    (θ : G ⋙ P ≅ R ⋙ H) (hs : ∀ T, J.essImage (R.obj (F.obj T))) :
    ∃ β : F ⋙ R ≅ P ⋙ J, ∀ T,
      b.homEquiv _ _ (β.inv.app T) = P.map (a.unit.app T) ≫ θ.hom.app (F.obj T) := by
  let t : P ⋙ J ⟶ F ⋙ R :=
    { app T := (b.homEquiv _ _).symm (P.map (a.unit.app T) ≫ θ.hom.app (F.obj T))
      naturality T T' f := by
        apply (b.homEquiv _ _).injective
        change b.homEquiv _ _ (J.map (P.map f) ≫ _) =
          b.homEquiv _ _ (_ ≫ R.map (F.map f))
        rw [b.homEquiv_naturality_left, b.homEquiv_naturality_right]
        simp only [Functor.comp_obj, Equiv.apply_symm_apply]
        have hn := θ.hom.naturality (F.map f)
        dsimp only [Functor.comp_map] at hn
        rw [Category.assoc, ← hn]
        simp only [← Category.assoc, ← P.map_comp]
        rw [← a.unit_naturality f] }
  have ht (T) : IsIso (t.app T) := by
    have : IsIso (a.unit.app T) := by infer_instance
    have hT : IsIso (b.counit.app (R.obj (F.obj T))) :=
      (b.isIso_counit_app_iff_mem_essImage).2 (hs T)
    change IsIso ((b.homEquiv _ _).symm _)
    rw [Adjunction.homEquiv_counit]
    have : IsIso (P.map (a.unit.app T) ≫ θ.hom.app (F.obj T)) := by infer_instance
    exact IsIso.comp_isIso' (J.map_isIso _) hT
  have : IsIso t := (NatTrans.isIso_iff_isIso_app t).2 ht
  refine ⟨(asIso t).symm, ?_⟩
  intro T
  exact (b.homEquiv _ _).apply_symm_apply _

private theorem underivedOpenSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W Y X : Scheme.{u}}
    (r : W ⟶ X) (i : Y ⟶ X) [IsOpenImmersion i] :
    ∃ β : openImmersionLowerShriek Λ i ⋙ upperStar Λ r ≅
        upperStar Λ (pullback.snd r i) ⋙ openImmersionLowerShriek Λ (pullback.fst r i),
      ∀ T, (openImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r i)).homEquiv
          _ _ (β.inv.app T) =
        (upperStar Λ (pullback.snd r i)).map
            ((openImmersionLowerShriekUpperStarAdjunction Λ i).unit.app T) ≫
          (openSquareModulePullbackIso Λ r i).hom.app
            ((openImmersionLowerShriek Λ i).obj T) := by
  apply squareOfEssImage (openImmersionLowerShriek Λ i) (upperStar Λ i)
    (upperStar Λ r) (upperStar Λ (pullback.snd r i))
    (openImmersionLowerShriek Λ (pullback.fst r i))
    (upperStar Λ (pullback.fst r i))
    (openImmersionLowerShriekUpperStarAdjunction Λ i)
    (openImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r i))
    (openSquareModulePullbackIso Λ r i)
  intro T
  apply mem_essImage_openImmersionLowerShriek_of_mem_essImage
  let e := (Mod.forget _).mapIso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ r)).app
      (((ProEtale.upperStar Ab.{u + 1} r).mapMod _).obj
        ((openImmersionLowerShriek Λ i).obj T)))
  let e' := e ≪≫ ((ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1}
    (IsPullback.of_hasPullback r i).flip).app T.X).symm
  exact ⟨_, ⟨e'.symm⟩⟩

private theorem commShiftOfEssSurj
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (L : E ⥤ C) [L.CommShift ℤ] [L.EssSurj]
    [NatTrans.CommShift (Functor.whiskerLeft L τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_whiskerLeft τ L
  intro X
  exact ⟨L.objPreimage X, (L.objObjPreimageIso X).inv, inferInstance⟩

private theorem exactSquareDerived
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    [Abelian C] [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D]
    (F : C ⥤ A) (R : A ⥤ D) (P : C ⥤ B) (J : B ⥤ D)
    [F.Additive] [R.Additive] [P.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (β : F ⋙ R ≅ P ⋙ J) :
    ∃ e : F.mapDerivedCategory ⋙ R.mapDerivedCategory ≅
        P.mapDerivedCategory ⋙ J.mapDerivedCategory,
      (∀ K : CochainComplex C ℤ,
        e.hom.app (DerivedCategory.Q.obj K) ≫
          J.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
          J.mapDerivedCategoryFactors.hom.app
            ((P.mapHomologicalComplex (.up ℤ)).obj K) =
        R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          R.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).hom.app K ≫
              (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ J)) (.up ℤ)).inv.app K)) ∧
      NatTrans.CommShift e.hom ℤ := by
  let eF : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ R.mapDerivedCategory) ≅
      (F.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors R.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ R.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  let eP : DerivedCategory.Q ⋙ (P.mapDerivedCategory ⋙ J.mapDerivedCategory) ≅
      (P.mapHomologicalComplex (.up ℤ) ⋙ J.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight P.mapDerivedCategoryFactors J.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ J.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  let c := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex β (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ J)) (.up ℤ)).symm
  let h := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (DerivedCategory D)
  let e : F.mapDerivedCategory ⋙ R.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ J.mapDerivedCategory :=
    h.preimageIso (eF ≪≫ Functor.isoWhiskerRight c DerivedCategory.Q ≪≫ eP.symm)
  have he : Functor.whiskerLeft DerivedCategory.Q e.hom =
      eF.hom ≫ Functor.whiskerRight c.hom DerivedCategory.Q ≫ eP.inv :=
    h.map_preimage _
  refine ⟨e, ?_, ?_⟩
  · intro K
    have hh := congr_app he K
    dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app] at hh
    rw [hh]
    have fac (K) : eP.inv.app K ≫
        J.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
        J.mapDerivedCategoryFactors.hom.app
          ((P.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := by
      have hp : eP.hom.app K =
          J.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
            J.mapDerivedCategoryFactors.hom.app
              ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
        dsimp only [eP, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
          Functor.associator_hom_app, Functor.associator_inv_app,
          Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
          Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.comp_obj]
        simp only [Category.id_comp, Category.comp_id]
      rw [← hp, Iso.inv_hom_id_app]
    rw [Category.assoc, Category.assoc, fac, Category.comp_id]
    simp only [eF, c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.comp_obj, Category.comp_id, Category.id_comp, Category.assoc,
      Functor.map_comp]
    rfl
  · have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q e.hom) ℤ := by
      rw [he]
      dsimp only [eF, eP, c]
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv]
      have : NatTrans.CommShift (NatIso.mapHomologicalComplex β (.up ℤ)).hom ℤ :=
        NatTrans.commShift_mapHomologicalComplex β.hom
      infer_instance
    exact commShiftOfEssSurj (C := DerivedCategory C) (D := DerivedCategory D)
      (E := CochainComplex C ℤ)
      (F := F.mapDerivedCategory ⋙ R.mapDerivedCategory)
      (G := P.mapDerivedCategory ⋙ J.mapDerivedCategory)
      e.hom (DerivedCategory.Q (C := C))


private theorem upperStarCongr_hom_app {S T : Scheme.{u}} {f g : S ⟶ T}
    (h : f = g) (M : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :
    (ProEtale.upperStarCongr Ab.{u + 1} h).hom.app M =
      (eqToHom (congrArg (ProEtale.upperStar Ab.{u + 1}) h)).app M := by
  subst h
  unfold ProEtale.upperStarCongr
  rfl

private theorem upperStarCongr_symm {S T : Scheme.{u}} {f g : S ⟶ T}
    (h : f = g) : (ProEtale.upperStarCongr Ab.{u + 1} h).symm =
      ProEtale.upperStarCongr Ab.{u + 1} h.symm := by
  subst h
  unfold ProEtale.upperStarCongr
  rfl

private theorem upperStarCompIso_symm {S X Y Z : Scheme.{u}}
    (a : S ⟶ X) (b : X ⟶ Z) (c : S ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d) :
    (ProEtale.upperStarCompIso Ab.{u + 1} h).symm =
      ProEtale.upperStarCompIso Ab.{u + 1} h.symm := by
  simp only [upperStarCompIso, Iso.trans_symm, Iso.symm_symm_eq, upperStarCongr_symm,
    Iso.trans_assoc]

private theorem upperStarCompIso_inv_app {S X Y Z : Scheme.{u}}
    (a : S ⟶ X) (b : X ⟶ Z) (c : S ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d)
    (M : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    (ProEtale.upperStarCompIso Ab.{u + 1} h).inv.app M =
      (ProEtale.upperStarComp Ab.{u + 1} c d).inv.app M ≫
        (eqToHom (congrArg (ProEtale.upperStar Ab.{u + 1}) h.symm)).app M ≫
        (ProEtale.upperStarComp Ab.{u + 1} a b).hom.app M := by
  change (ProEtale.upperStarCompIso Ab.{u + 1} h).symm.hom.app M = _
  rw [upperStarCompIso_symm]
  unfold ProEtale.upperStarCompIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [upperStarCongr_hom_app]

private theorem compFromFive {C : Type*} [Category C]
    {A B C₁ D E F : C} {s : A ⟶ D} {a : A ⟶ B} {b : B ⟶ C₁}
    {c : C₁ ⟶ D} {d : D ⟶ E} {e : E ⟶ F} {f : A ⟶ F}
    (h : s = a ≫ b ≫ c) (hh : a ≫ b ≫ c ≫ d ≫ e = f) : s ≫ d ≫ e = f := by
  rw [h, Category.assoc, Category.assoc]
  exact hh

private theorem coefficientMap_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {S T : Scheme.{u}} (f : S ⟶ T) :
    condensedPullbackHom Λ f = (upperStarFromPointComp f).hom.app Λ := rfl

private theorem coefficientSquare
    {S X Y Z : Scheme.{u}} (a : S ⟶ X) (b : X ⟶ Z)
    (c : S ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (ProEtale.upperStarCompIso Ab.{u + 1} h).inv.app ((upperStarFromPoint Z).obj Λ) ≫
        (ProEtale.upperStar Ab.{u + 1} a).map ((upperStarFromPointComp b).hom.app Λ) ≫
        (upperStarFromPointComp a).hom.app Λ =
      (ProEtale.upperStar Ab.{u + 1} c).map ((upperStarFromPointComp d).hom.app Λ) ≫
        (upperStarFromPointComp c).hom.app Λ := by
  exact compFromFive (C := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (upperStarCompIso_inv_app a b c d h ((upperStarFromPoint Z).obj Λ))
    (profinite_point_pullback_abelian_coherence.2.2.2 _ _ _ _ c d a b h.symm Λ)

private theorem ringSquare_inv_app {W Y X : Scheme.{u}} (r : W ⟶ X) (i : Y ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (ringSheafSquareComparison r i).inv.app M =
      (ProEtale.upperStarCompIso Ab.{u + 1}
        (pullback.condition (f := r) (g := i))).inv.app M := by
  exact congrArg (fun e : ProEtale.upperStar Ab.{u + 1} r ⋙
      ProEtale.upperStar Ab.{u + 1} (pullback.fst r i) ≅
      ProEtale.upperStar Ab.{u + 1} i ⋙
      ProEtale.upperStar Ab.{u + 1} (pullback.snd r i) => e.inv.app M)
    (ringSheafSquareComparison_eq r i)

private theorem pullbackCoefficientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {W Y X : Scheme.{u}} (r : W ⟶ X) (i : Y ⟶ X) :
    (ringSheafSquareComparison r i).inv.app ((upperStarFromPoint X).obj Λ) ≫
        (ProEtale.upperStar Ab.{u + 1} (pullback.fst r i)).map
          ((upperStarFromPointComp r).hom.app Λ) ≫
          (upperStarFromPointComp (pullback.fst r i)).hom.app Λ =
      (ProEtale.upperStar Ab.{u + 1} (pullback.snd r i)).map
          ((upperStarFromPointComp i).hom.app Λ) ≫
          (upperStarFromPointComp (pullback.snd r i)).hom.app Λ := by
  rw [ringSquare_inv_app]
  exact coefficientSquare (S := pullback r i) (X := W) (Y := Y) (Z := X)
    (pullback.fst r i) r (pullback.snd r i) i
    (pullback.condition (f := r) (g := i)) Λ

private theorem coefficientComposite_eq
    {S T V : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ V)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (ProEtale.upperStar Ab.{u + 1} f).map (condensedPullbackHom Λ g) ≫
        condensedPullbackHom Λ f =
      (ProEtale.upperStar Ab.{u + 1} f).map ((upperStarFromPointComp g).hom.app Λ) ≫
        (upperStarFromPointComp f).hom.app Λ := by
  exact congrArg₂ (fun
      (a : (ProEtale.upperStar Ab.{u + 1} g).obj (condensedRingObj Λ V) ⟶
        condensedRingObj Λ T)
      (b : (ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ T) ⟶
        condensedRingObj Λ S) => (ProEtale.upperStar Ab.{u + 1} f).map a ≫ b)
    (coefficientMap_eq Λ g) (coefficientMap_eq Λ f)

attribute [local irreducible] ProEtale.upperStar ProEtale.upperStarFromPoint
attribute [local irreducible] upperStar openImmersionLowerShriek
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private theorem squareInverseCoefficient_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {W Y X : Scheme.{u}} (r : W ⟶ X) (i : Y ⟶ X) :
    (ringSheafSquareComparison r i).inv.app (condensedRingObj Λ X) =
      (ringSheafSquareComparison r i).inv.app ((upperStarFromPoint X).obj Λ) := rfl

private theorem transportComposite {C : Type*} [Category C]
    {X Y Z : C} {a a' : X ⟶ Y} {b b' : Y ⟶ Z} {c c' : X ⟶ Z}
    (ha : a = a') (hb : b = b') (hc : c = c') (h : a' ≫ b' = c') : a ≫ b = c := by
  rw [ha, hb, hc]
  exact h

private theorem coefficientSquareTarget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {W Y X : Scheme.{u}} (r : W ⟶ X) (i : Y ⟶ X) :
    (ringSheafSquareComparison r i).inv.app (condensedRingObj Λ X) ≫
        (ProEtale.upperStar Ab.{u + 1} (pullback.fst r i)).map
          (condensedPullbackHom Λ r) ≫ condensedPullbackHom Λ (pullback.fst r i) =
      (ProEtale.upperStar Ab.{u + 1} (pullback.snd r i)).map
          (condensedPullbackHom Λ i) ≫ condensedPullbackHom Λ (pullback.snd r i) := by
  exact transportComposite
    (C := Sheaf (Scheme.ProEt.topology (pullback r i)) Ab.{u + 1})
    (squareInverseCoefficient_eq Λ r i)
    (coefficientComposite_eq (pullback.fst r i) r Λ)
    (coefficientComposite_eq (pullback.snd r i) i Λ)
    (pullbackCoefficientSquare Λ r i)

/-- Open base change with its coefficient equation, specified adjunct, exactness,
localization normalization and compatibility with every integer shift.

Source: blueprint main-20261015, det-sf-open-closed-sequence-ring-sheaf, proof (4);
lem-sfb-eta-comp; Stacks Project, Tag 04VG, lemma-properties-left-localization.
(blueprint: lem-sfb-condensed-open-square-scalar-comparison).

Proof:
1. Specialize the existing profinite-point square coherence equation to the pullback
   square. Inverting the square comparison reverses its two routes, giving the stated
   coefficient equation.
2. Construct the inverse module comparison by the specified open Hom-equivalence,
   applied to the open unit followed by the specified module square comparison.
   Naturality follows from naturality of these three maps.
3. The open unit is invertible by full faithfulness. Extension along the coefficient
   isomorphism identifies the underlying pullback with ordinary abelian pullback.
   Abelian open base change and the module essential-image criterion show that its
   target lies in the essential image of extension by zero. The open counit there is
   invertible, so the adjunct formula makes the inverse comparison invertible.
4. The four module functors have the required exactness instances. Their exact
   derived factorization isomorphisms transport the termwise comparison to a natural
   isomorphism after precomposition by Q. Fully faithful localization gives its
   preimage, and its map-preimage equation gives the displayed normalization.
5. Termwise maps, termwise compositors and the exact derived factorizations commute
   with every integer shift. Essential surjectivity of Q detects this property for
   the derived comparison itself.
-/
theorem condensed_open_square_scalar_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {W Y X : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (r : W ⟶ X) (i : Y ⟶ X) [IsOpenImmersion i.left] [QuasiCompact i.left] :
    ((ringSheafSquareComparison r.left i.left).inv.app (condensedRingObj Λ X.left) ≫
        (ProEtale.upperStar Ab.{u + 1} (pullback.fst r.left i.left)).map
          (condensedPullbackHom Λ r.left) ≫
        condensedPullbackHom Λ (pullback.fst r.left i.left) =
      (ProEtale.upperStar Ab.{u + 1} (pullback.snd r.left i.left)).map
          (condensedPullbackHom Λ i.left) ≫
        condensedPullbackHom Λ (pullback.snd r.left i.left)) ∧
    PreservesFiniteLimits (upperStar Λ r.left) ∧
    PreservesFiniteColimits (upperStar Λ r.left) ∧
    PreservesFiniteLimits (openImmersionLowerShriek Λ i.left) ∧
    PreservesFiniteColimits (openImmersionLowerShriek Λ i.left) ∧
    PreservesFiniteLimits (upperStar Λ (pullback.snd r.left i.left)) ∧
    PreservesFiniteColimits (upperStar Λ (pullback.snd r.left i.left)) ∧
    PreservesFiniteLimits (openImmersionLowerShriek Λ (pullback.fst r.left i.left)) ∧
    PreservesFiniteColimits (openImmersionLowerShriek Λ (pullback.fst r.left i.left)) ∧
    ∃ β : openImmersionLowerShriek Λ i.left ⋙ upperStar Λ r.left ≅
        upperStar Λ (pullback.snd r.left i.left) ⋙
          openImmersionLowerShriek Λ (pullback.fst r.left i.left),
      (∀ T : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ Y.left),
        (openImmersionLowerShriekUpperStarAdjunction Λ
          (pullback.fst r.left i.left)).homEquiv _ _ (β.inv.app T) =
        (upperStar Λ (pullback.snd r.left i.left)).map
            ((openImmersionLowerShriekUpperStarAdjunction Λ i.left).unit.app T) ≫
          (openSquareModulePullbackIso Λ r.left i.left).hom.app
            ((openImmersionLowerShriek Λ i.left).obj T)) ∧
      ∃ βD : (openImmersionLowerShriek Λ i.left).mapDerivedCategory ⋙
            (upperStar Λ r.left).mapDerivedCategory ≅
          (upperStar Λ (pullback.snd r.left i.left)).mapDerivedCategory ⋙
            (openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory,
        (∀ K : CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
              (condensedRingObj Λ Y.left)) ℤ,
          βD.hom.app (DerivedCategory.Q.obj K) ≫
              (openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory.map
                ((upperStar Λ (pullback.snd r.left i.left)).mapDerivedCategoryFactors.hom.app K) ≫
              (Functor.mapDerivedCategoryFactors
                (openImmersionLowerShriek Λ (pullback.fst r.left i.left))).hom.app
                (((upperStar Λ (pullback.snd r.left i.left)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K) =
            (upperStar Λ r.left).mapDerivedCategory.map
                ((openImmersionLowerShriek Λ i.left).mapDerivedCategoryFactors.hom.app K) ≫
              (upperStar Λ r.left).mapDerivedCategoryFactors.hom.app
                (((openImmersionLowerShriek Λ i.left).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K) ≫
              DerivedCategory.Q.map (openSquareComplexComparison Λ r.left i.left β K)) ∧
        NatTrans.CommShift βD.hom ℤ := by
  refine ⟨?_, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  · exact coefficientSquareTarget Λ r.left i.left
  · have hb := underivedOpenSquare (W := W.left) (Y := Y.left) (X := X.left)
      Λ r.left i.left
    obtain ⟨β, hβ⟩ := hb
    refine ⟨β, hβ, ?_⟩
    let F := openImmersionLowerShriek Λ i.left
    let R := upperStar Λ r.left
    let P := upperStar Λ (pullback.snd r.left i.left)
    let J := openImmersionLowerShriek Λ (pullback.fst r.left i.left)
    exact exactSquareDerived
      (C := Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj Λ Y.left))
      (A := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left))
      (B := Mod (Sheaf (Scheme.ProEt.topology (pullback r.left i.left)) Ab.{u + 1})
        (condensedRingObj Λ (pullback r.left i.left)))
      (D := Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
        (condensedRingObj Λ W.left)) F R P J β

end AlgebraicGeometry.ProEtale.CondensedRing
