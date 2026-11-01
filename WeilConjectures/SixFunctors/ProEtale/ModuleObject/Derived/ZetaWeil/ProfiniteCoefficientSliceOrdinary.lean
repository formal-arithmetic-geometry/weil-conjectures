/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.CommutativeConstantSliceRestriction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction

/-! # Ordinary coefficient extension on the profinite slice

Source: Hemo--Richarz--Scholbach, (3.1)--(3.2), Remark 3.2;
Stacks Project, Modules on Sites, Tags 03CY, 03DH and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace SliceCoefficientProof

universe a b r m
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}

private def restriction {R : Sheaf J RingCat.{r}} (U : C)
    {R' : Sheaf (J.over U) RingCat.{r}} (c : R' ≅ R.over U) :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} R' :=
  SheafOfModules.overFunctor R U ⋙ SheafOfModules.restrictScalars c.hom

private def rightSquare [HasBinaryProducts C] {R S : Sheaf J RingCat.{r}}
    (U : C) {R' S' : Sheaf (J.over U) RingCat.{r}}
    (c : R' ≅ R.over U) (d : S' ≅ S.over U) (α : R ⟶ S) (β : R' ⟶ S')
    (h : c.hom ≫ (J.overPullback RingCat.{r} U).map α = β ≫ d.hom) :
    (SheafOfModules.restrictScalars.{m} d.inv ⋙
      SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := S) U)) ⋙
        SheafOfModules.restrictScalars α ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars c.inv ⋙
        SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) U) := by
  let G := (Over.star U).sheafPushforwardContinuous RingCat.{r} J (J.over U)
  let p := SheafOfModules.pushforwardOver (R := R) U
  let q := SheafOfModules.pushforwardOver (R := S) U
  have h' : (J.overPullback RingCat.{r} U).map α ≫ d.inv = c.inv ≫ β := by
    calc
      _ = c.inv ≫ (c.hom ≫ (J.overPullback RingCat.{r} U).map α) ≫ d.inv := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = c.inv ≫ (β ≫ d.hom) ≫ d.inv := by rw [h]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn : α ≫ q = p ≫ G.map ((J.overPullback RingCat.{r} U).map α) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact (α.hom.naturality Limits.prod.snd.op).symm
  have hs : α ≫ (q ≫ G.map d.inv) = (p ≫ G.map c.inv) ≫ G.map β := by
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp, h', G.map_comp]
    simp only [Category.assoc]
  let i := SheafOfModules.pushforwardComp (F := Over.star U) (G := 𝟭 (Over U)) q d.inv
  let j := SheafOfModules.pushforwardComp (F := Over.star U) (G := 𝟭 (Over U)) p c.inv
  exact Functor.isoWhiskerRight i _ ≪≫
    SheafOfModules.pushforwardComp (F := 𝟭 C) (G := Over.star U) α (q ≫ G.map d.inv) ≪≫
    SheafOfModules.pushforwardCongr hs ≪≫
    (SheafOfModules.pushforwardComp (F := Over.star U) (G := 𝟭 (Over U))
      (p ≫ G.map c.inv) β).symm ≪≫ Functor.isoWhiskerLeft _ j.symm

end SliceCoefficientProof

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.Obj

private def sliceRingIso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) :
    (condensedSectionRing Λ.X).over S ≅
      Evaluation.ringSheaf ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ.X S) := by
  let J := coherentTopology Profinite.{u}
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (Over.forget S) Ab.{u + 1} (J.over S) J
  let z := ((Functor.mapCommMonCompIso (F := sheafToPresheaf J Ab.{u + 1})
      (G := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj (Over.forget S).op)).symm ≪≫
    Functor.mapCommMonNatIso e ≪≫
    Functor.mapCommMonCompIso (F := J.overPullback Ab.{u + 1} S)
      (G := sheafToPresheaf (J.over S) Ab.{u + 1})).app (CommMon.mk Λ.X)
  let w := (Monoidal.commMonFunctorCategoryEquivalence (Over S)ᵒᵖ Ab.{u + 1}).functor.mapIso z
  exact ObjectProperty.isoMk _ (Functor.isoWhiskerRight w
    InternalAbelianSheafModule.commMonToRing)

private def sliceModules (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) :=
  SliceCoefficientProof.restriction
    (R := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ.X)) S
    ((sheafCompose ((coherentTopology Profinite.{u}).over S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (sliceRingIso Λ S).symm)

attribute [local irreducible] sliceRingIso

end AlgebraicGeometry.ProEtale.CondensedRing
