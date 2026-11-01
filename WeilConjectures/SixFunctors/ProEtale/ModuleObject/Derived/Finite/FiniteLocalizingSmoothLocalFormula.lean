/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import WeilConjectures.SixFunctors.Etale.Derived.Orientation
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-!
# The local smooth formula for the finite-coefficient localizing adjoint

This separates the smooth tensor calculation from preservation for arbitrary finite-type maps.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Reflect a two-pullback formula through three coefficient equivalences. Keeping this
composition abstract prevents unfolding the concrete localization functors. -/
@[irreducible] private noncomputable def transportLocalFormula
    {D C₁ C₂ C₃ E₁ E₂ E₃ : Type*}
    [Category D] [Category C₁] [Category C₂] [Category C₃]
    [Category E₁] [Category E₂] [Category E₃]
    (I : D ⥤ C₁) (R : D ⥤ C₂) (F : C₁ ⥤ C₂) (J : C₂ ⥤ C₃) (S : C₃ ⥤ C₃)
    (e₁ : C₁ ≌ E₁) (e₂ : C₂ ≌ E₂) (e₃ : C₃ ≌ E₃)
    (R' : D ⥤ E₂) (F' : E₁ ⥤ E₂) (J' : E₂ ⥤ E₃) (S' : E₃ ⥤ E₃)
    (er : R ⋙ e₂.functor ≅ R')
    (ef : F ⋙ e₂.functor ≅ e₁.functor ⋙ F')
    (ej : J ⋙ e₃.functor ≅ e₂.functor ⋙ J')
    (es : S ⋙ e₃.functor ≅ e₃.functor ⋙ S')
    (eo : R' ⋙ J' ≅ I ⋙ e₁.functor ⋙ F' ⋙ J' ⋙ S') :
    R ⋙ J ≅ I ⋙ F ⋙ J ⋙ S := by
  let el : (R ⋙ J) ⋙ e₃.functor ≅ R' ⋙ J' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R ej ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight er J'
  let rr : (I ⋙ F ⋙ J ⋙ S) ⋙ e₃.functor ≅
      I ⋙ e₁.functor ⋙ F' ⋙ J' ⋙ S' :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft I (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft F (Functor.associator _ _ _)) ≪≫
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft J es)) ≪≫
      Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft F
        ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ej S' ≪≫
          Functor.associator _ _ _)) ≪≫
      Functor.isoWhiskerLeft I ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ef (J' ⋙ S') ≪≫ Functor.associator _ _ _)
  exact (e₃.fullyFaithfulFunctor.whiskeringRight _).preimageIso (el ≪≫ eo ≪≫ rr.symm)

/-- Reassociate the local formula before instantiating concrete derived functors. -/
@[irreducible] private noncomputable def reassociateLocalFormula
    {D A B C₁ C₂ C₃ : Type*}
    [Category D] [Category A] [Category B]
    [Category C₁] [Category C₂] [Category C₃]
    (V : D ⥤ A) (G : A ⥤ B) (iX : B ⥤ C₂) (iY : A ⥤ C₁)
    (F : C₁ ⥤ C₂) (J : C₂ ⥤ C₃) (S : C₃ ⥤ C₃)
    (e : (V ⋙ G ⋙ iX) ⋙ J ≅ (V ⋙ iY) ⋙ F ⋙ J ⋙ S) :
    V ⋙ G ⋙ iX ⋙ J ≅ V ⋙ iY ⋙ F ⋙ J ⋙ S :=
  (Functor.associator V (G ⋙ iX) J ≪≫
    Functor.isoWhiskerLeft V (Functor.associator G iX J)).symm ≪≫ e ≪≫
    Functor.associator V iY (F ⋙ J ⋙ S)

private noncomputable def encodingPullbackIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A]
    {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : FiniteDiscreteOrdinary.Encoding A T) (eU : FiniteDiscreteOrdinary.Encoding A U) :
    (upperStar (FiniteDiscreteOrdinary.coefficient A) f).mapDerivedCategory ⋙
        eU.fixedDerived.functor ≅
      eT.fixedDerived.functor ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : lowerStar (FiniteDiscreteOrdinary.coefficient A) f ⋙ ET.functor ≅
      EU.functor ⋙ R :=
    FiniteDiscreteOrdinary.encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (upperStarLowerStarAdjunction (FiniteDiscreteOrdinary.coefficient A) f).comp
    EU.toAdjunction
  let e := (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm
  letI : ET.functor.Additive :=
    inferInstanceAs (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive :=
    inferInstanceAs (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso _ _

private noncomputable def etaleSmoothLocalIso
    (B : Type (u + 1)) [CommRing B] [Finite B]
    {X Y U : Scheme.{u}} [HasInvertibleExponent B X]
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : U ⟶ X)
    (e : (Etale.upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
        (Etale.dualizingComplex B f) ≅
      (MonoidalCategoryStruct.tensorUnit (_root_.DerivedCategory
        (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)))) ⟦2 * (d : ℤ)⟧) :
    Etale.rightDerivedUpperShriek B f ⋙
        (Etale.upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor ⋙
        (Etale.upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor ⋙
          shiftFunctor _ (2 * (d : ℤ)) := by
  let C := ModuleCat.{u + 1} B
  let P := (Etale.upperStar C f).leftDerivedFunctor
  let J := (Etale.upperStar C j).leftDerivedFunctor
  let W := Etale.dualizingComplex B f
  let R := Etale.rightDerivedUpperShriek B f
  letI := Etale.derivedBraidedCategory B X
  letI := Etale.derivedBraidedCategory B Y
  letI := Etale.derivedBraidedCategory B U
  have hθ : ∀ K, IsIso (Etale.dualizingComplexTensorMap B f K) := by
    obtain ⟨_, _, _, _, hθ⟩ := Etale.exists_dualizingComplex_iso_and_tensor B f d
    exact hθ
  let θ : P ⋙ MonoidalCategory.tensorLeft W ≅ R :=
    NatIso.ofComponents (fun K ↦ by
      have := hθ K
      exact asIso (Etale.dualizingComplexTensorMap B f K)) (by
      intro K L a
      dsimp only [Functor.comp_map, asIso_hom, MonoidalCategory.tensorLeft,
        MonoidalCategory.curriedTensor, Etale.dualizingComplexTensorMap,
        Etale.lowerShriekRightAdjointUnitTensorMap,
        Etale.lowerShriekRightAdjointTensorMap, W, Etale.dualizingComplex]
      rw [← Category.assoc]
      erw [(Etale.rightDerivedUpperShriekAdjunction B f).projectionTensorMap_naturality_right
        (fun M N ↦ ((Etale.projectionMap C f).app M).app N)
        (Etale.projectionMap_app_app_naturality_right f) (𝟙_ _) a]
      rw [Category.assoc, ← R.map_comp, leftUnitor_naturality, R.map_comp,
        Category.assoc])
  letI := Etale.leftDerivedUpperStarMonoidal C j
  let t : MonoidalCategory.tensorLeft (J.obj W) ≅
      shiftFunctor _ (2 * (d : ℤ)) :=
    (MonoidalCategory.curriedTensor _).mapIso e ≪≫
      Etale.tensorLeftUnitShiftIso U (2 * (d : ℤ))
  exact Functor.isoWhiskerRight θ.symm J ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P (Functor.Monoidal.commTensorLeft J W).symm ≪≫
    Functor.isoWhiskerLeft P (Functor.isoWhiskerLeft J t)

private theorem ordinary_constructible_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

private theorem ordinary_ctf_iff (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    FiniteDiscreteOrdinary.ordinaryCtf A T K ↔
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  have hb : FiniteDiscreteOrdinary.ordinaryBoundedConstructible A T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
    constructor
    · rintro ⟨hb, hc⟩
      apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A) hb
      intro n
      exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} A)
        ((ordinary_constructible_iff A T _).mp (hc n))
    · intro h
      have hi := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ h
      exact ⟨hi.1, fun n ↦ (ordinary_constructible_iff A T _).mpr (hi.2 n)⟩
  exact and_congr hb Iff.rfl

private theorem coefficient_exponent (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (A : Type u) [CommRing A]
    (hA : ∃ r : ℕ, ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0) :
    HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) := by
  obtain ⟨r, hr⟩ := hA
  have hℓ : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k) (Fact.out : ℓ.Prime)
      (Fact.out : ringChar k ≠ ℓ)
  exact ⟨ℓ ^ r, pow_pos (Fact.out : ℓ.Prime).pos _, hr,
    by
      simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
        (Scheme.ΓSpecIso (.of k)).inv.hom⟩

private abbrev ordinaryProperty (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T

private noncomputable def ordinary_compactification_iso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (c : Compactification f) :
    (ordinaryProperty A X).ι ⋙
        ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ≅
      (ordinaryProperty A X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let P := DerivedCategory.plusEtaleOrigin B X
  let E := (comparisonUpperStarPlusEtaleOrigin B X).asEquivalence
  let I : (ordinaryProperty A X).FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.ιOfLE (fun _ hK ↦ hK.plusEtaleOrigin)
  let O := I ⋙ E.inverse
  let e : O ⋙ DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar B X).mapDerivedCategory ≅ (ordinaryProperty A X).ι :=
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight E.counitIso P.ι)
  exact (Functor.isoWhiskerRight e (ProEtale.rightDerivedLowerShriek B f)).symm ≪≫
    Functor.isoWhiskerLeft O (rightDerivedLowerShriekCompactificationIso
      (ULift.{u + 1} A) c) ≪≫
    Functor.isoWhiskerRight e (ProEtale.rightDerivedLowerShriekOfCompactification B c)

private theorem ordinary_small_adjunction
    (A : Type u) [CommRing A] [Finite A] (k : Type u) [Field k]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [QuasiCompact s]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [HasInvertibleExponent (ULift.{u + 1} A) Y] (c : Compactification f) :
    ∃ (hF : ∀ K, ordinaryProperty A X K → ordinaryProperty A Y
          ((ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K))
      (R : (ordinaryProperty A Y).FullSubcategory ⥤
        (ordinaryProperty A X).FullSubcategory),
      Nonempty ((ordinaryProperty A Y).lift ((ordinaryProperty A X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)
        (fun K ↦ hF K.obj K.property) ⊣ R) ∧
      Nonempty (R ⋙ (ordinaryProperty A X).ι ≅ (ordinaryProperty A Y).ι ⋙
        ProEtale.rightDerivedUpperShriek (ULift.{u + 1} A) f) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Q := ordinaryProperty A Y
  let P := ordinaryProperty A X
  let e := ordinary_compactification_iso A f c
  have hf := fun K (hK : P K) ↦ constructibleFiniteTor_rightDerivedLowerShriek
    (ULift.{u + 1} A) s f hK
  have hc (K) (hK : P K) : Q
      ((ProEtale.rightDerivedLowerShriekOfCompactification B c).obj K) :=
    Q.prop_of_iso (e.app ⟨K, hK⟩) (hf K hK)
  let R := P.lift (Q.ι ⋙ ProEtale.rightDerivedUpperShriek (ULift.{u + 1} A) f)
    (fun K ↦ constructibleFiniteTor_rightDerivedUpperShriek (ULift.{u + 1} A) s f K.property)
  let L := Q.lift (P.ι ⋙ ProEtale.rightDerivedLowerShriek B f)
    (fun K ↦ hf K.obj K.property)
  let Lc := Q.lift (P.ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification B c)
    (fun K ↦ hc K.obj K.property)
  let ec : L ≅ Lc := (Q.fullyFaithfulι.whiskeringRight _).preimageIso e
  exact ⟨hc, R, ⟨(DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction
    (ULift.{u + 1} A) s f).ofNatIsoLeft ec⟩, ⟨Iso.refl _⟩⟩

private noncomputable def overTrivialization
    (B : Type (u + 1)) [CommRing B] {X : Scheme.{u}}
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C : Scheme.Cover.{u} Scheme.etalePrecoverage X) (i : C.I₀)
    (e : M.over (C.etalePrecoverageToEtale i) ≅
      (constantSheaf (X.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
        (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)) :
    (Etale.upperStar (ModuleCat.{u + 1} B) (C.f i)).obj M ≅
      MonoidalCategoryStruct.tensorUnit
        (Sheaf (C.X i).smallEtaleTopology (ModuleCat.{u + 1} B)) := by
  let U := C.etalePrecoverageToEtale i
  let E := Etale.overSheafEquiv U (ModuleCat.{u + 1} B)
  let c := (Etale.overEquiv U).constantSheafSheafCongrIso
    (X.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} B)
    Over.mkIdTerminal
  exact (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} B) U M).symm ≪≫
    E.functor.mapIso e ≪≫ c.app (ModuleCat.of B B)

private noncomputable def trivializationPullback
    (B : Type (u + 1)) [CommRing B] {X U V : Scheme.{u}}
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (j : U ⟶ X) (g : V ⟶ U)
    (e : (Etale.upperStar (ModuleCat.{u + 1} B) j).obj M ≅
      MonoidalCategoryStruct.tensorUnit (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (Etale.upperStar (ModuleCat.{u + 1} B) (g ≫ j)).obj M ≅
      MonoidalCategoryStruct.tensorUnit (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
  (Etale.upperStarComp (ModuleCat.{u + 1} B) g j).app M ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} B) g).mapIso e ≪≫
    (Functor.Monoidal.εIso (Etale.upperStar (ModuleCat.{u + 1} B) g)).symm

private noncomputable def ordinarySmoothLocalIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [HasInvertibleExponent (ULift.{u + 1} A) X]
    (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : U ⟶ X)
    (e : (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ULift.{u + 1} A) f) ≅
      (MonoidalCategoryStruct.tensorUnit (_root_.DerivedCategory
        (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))))
          ⟦2 * (d : ℤ)⟧) :
    (ordinaryProperty A Y).ι ⋙
        ProEtale.rightDerivedUpperShriek (ULift.{u + 1} A) f ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory ≅
      (ordinaryProperty A Y).ι ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory ⋙
          shiftFunctor _ (2 * (d : ℤ)) := by
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  let Q := ordinaryProperty A Y
  let P := DerivedCategory.plusEtaleOrigin C Y
  let E := (comparisonUpperStarPlusEtaleOrigin C Y).asEquivalence
  let I : Q.FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.ιOfLE (fun _ hK ↦ hK.plusEtaleOrigin)
  let O := I ⋙ E.inverse ⋙ _root_.DerivedCategory.Plus.ι
  let N (T : Scheme.{u}) := (comparisonUpperStar C T).mapDerivedCategory
  let R := Etale.rightDerivedUpperShriek B f
  let J := (ProEtale.upperStar C j).mapDerivedCategory
  let Je := (Etale.upperStar C j).mapDerivedCategory
  let Pe := (Etale.upperStar C f).mapDerivedCategory
  let ν : O ⋙ N Y ≅ Q.ι :=
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight E.counitIso P.ι)
  let aν := derivedComparisonAdjunction C Y
  have hunit (K : Q.FullSubcategory) : IsIso (aν.unit.app (O.obj K)) :=
    isIso_derivedComparisonAdjunction_unit_app C Y _ (E.inverse.obj (I.obj K)).property
  let η : O ≅ O ⋙ N Y ⋙ (comparisonLowerStar C Y).rightDerivedFunctor :=
    NatIso.ofComponents (fun K ↦ by letI := hunit K; exact asIso (aν.unit.app (O.obj K)))
      (fun g ↦ by
        change O.map g ≫ aν.unit.app _ = aν.unit.app _ ≫ _
        exact aν.unit.naturality (O.map g))
  let er : Q.ι ⋙ ProEtale.rightDerivedUpperShriek B f ≅ O ⋙ R ⋙ N X :=
    Functor.isoWhiskerRight ν.symm (ProEtale.rightDerivedUpperShriek B f) ≪≫
      Functor.isoWhiskerRight η.symm (R ⋙ N X)
  let ej : (Etale.upperStar C j).leftDerivedFunctor ≅ Je :=
    Etale.leftDerivedUpperStarIsoMapDerivedCategory C j
  let ep : (Etale.upperStar C f).leftDerivedFunctor ≅ Pe :=
    Etale.leftDerivedUpperStarIsoMapDerivedCategory C f
  let es : R ⋙ Je ≅ Pe ⋙ Je ⋙ shiftFunctor _ (2 * (d : ℤ)) :=
    (Functor.isoWhiskerLeft R ej).symm ≪≫ etaleSmoothLocalIso B f d j e ≪≫
      Functor.isoWhiskerRight ep _ ≪≫
      Functor.isoWhiskerLeft Pe (Functor.isoWhiskerRight ej _)
  exact Functor.isoWhiskerRight er J ≪≫
    Functor.isoWhiskerLeft O (Functor.isoWhiskerLeft R
      (unboundedDirectImagePullbackIso B j)) ≪≫
    Functor.isoWhiskerLeft O (Functor.isoWhiskerRight es (N U)) ≪≫
    Functor.isoWhiskerLeft O (Functor.isoWhiskerLeft Pe
      (Functor.isoWhiskerLeft Je ((N U).commShiftIso (2 * (d : ℤ))))) ≪≫
    Functor.isoWhiskerLeft O (Functor.isoWhiskerLeft Pe
      (Functor.isoWhiskerRight (unboundedDirectImagePullbackIso B j).symm _)) ≪≫
    Functor.isoWhiskerLeft O
      (Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerRight (unboundedDirectImagePullbackIso B f).symm J) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Functor.associator _ _ _).symm _) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight ν _) _) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.associator _ _ _

/-- The smooth localizing exceptional adjoint is a shifted pullback on one common cover.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, final restriction and smooth-formula paragraph.

Proof:
1. Use the finite-discrete coefficient equivalence and the bounded-below etale-origin
comparison of compact support to identify the given adjoint, on bounded constructible
finite-Tor inputs, with the ordinary etale exceptional adjoint transported by comparison.
Transpose the ordinary counit. The comparison is invertible because maps from every shifted
constructible finite-Tor generator are bijective and both objects lie in their localizing
closure. Naturality follows from the counit and uniqueness of transposes.
2. Smooth tensor duality gives a single rank-one locally constant etale sheaf L and the
natural formula f^! K = f^* K tensor L[2d]. The finite etale Tate-twist lemma gives an etale
cover trivializing the actual twist A(d). Refine this cover with a cover trivializing L.
This refinement depends on f and the coefficient ring, and is independent of K.
3. On every member of this common cover, use these two trivializations and the tensor
unitors to obtain the natural shifted-pullback formula. Transport it by the exact etale to
pro-etale comparison and the coefficient equivalences. Their pullback and shift comparisons
identify its two functors with those displayed below. The pullback comparison also transports
the twist trivialization to the displayed ordinary pro-etale constant regular module.

Edge cases: d = 0 uses the zero shift; r = 0 forces the zero coefficient ring, whose regular
module and both functors are zero. Empty schemes admit the empty cover.

(blueprint: lem-sf-finite-localizing-smooth-local-formula) -/
theorem localizingExceptionalAdjoint_smoothLocalFormula
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X K →
      localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y
        ((rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj A) c.obj.obj).obj K))
    (G : (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory
      ⥤ (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).FullSubcategory)
    (adj : localizingLowerShriek (Profinite.continuousCoefficientRingObj A) c.obj.obj h ⊣ G)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (r : ℕ) (hAr : ((ℓ ^ r : ℕ) : ULift.{u + 1} A) = 0) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : 𝒰.I₀,
          Nonempty
            ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (𝒰.f i)).obj
                ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj
                  (finiteEtaleTateTwist X (ℓ ^ r) (ULift.{u + 1} A) hAr d)) ≅
              (constantSheaf (Scheme.ProEt.topology (𝒰.X i))
                (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
                  (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A))) ∧
          Nonempty
            (((show ObjectProperty _ from fun K : (localizingClosureProEtale
                  (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory ↦
                (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) Y ⊓
                  fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L) K.obj)).ι ⋙
                G ⋙ (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) X).ι ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory ≅
              ((show ObjectProperty _ from fun K : (localizingClosureProEtale
                  (Profinite.continuousCoefficientRingObj A) Y).FullSubcategory ↦
                (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) Y ⊓
                  fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L) K.obj)).ι ⋙
                (localizingClosureProEtale (Profinite.continuousCoefficientRingObj A) Y).ι ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) f).mapDerivedCategory ⋙
                (upperStar (Profinite.continuousCoefficientRingObj A) (𝒰.f i)).mapDerivedCategory ⋙
                shiftFunctor _ (2 * (d : ℤ))) := by
  classical
  change (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).FullSubcategory
    ⥤ (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).FullSubcategory at G
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : HasCompactification f := c.obj.obj.hasCompactification
  have : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) :=
    coefficient_exponent ℓ k A ⟨r, hAr⟩
  have : HasInvertibleExponent (ULift.{u + 1} A) Y :=
    HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
  obtain ⟨E, hE, hcomp⟩ := FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence A
  let P (T : Scheme.{u}) := constantModelBoundedConstructible
    (FiniteDiscreteOrdinary.coefficient A) T ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
  let Q := ordinaryProperty A
  have hX (K) : P X K ↔ Q X ((E X).fixedDerived.functor.obj K) :=
    ((hE X).2.2.2.2.1 K).trans (ordinary_ctf_iff A X _)
  have hY (K) : P Y K ↔ Q Y ((E Y).fixedDerived.functor.obj K) :=
    ((hE Y).2.2.2.2.1 K).trans (ordinary_ctf_iff A Y _)
  let eX : (P X).FullSubcategory ≌ (Q X).FullSubcategory :=
    (E X).fixedDerived.congrFullSubcategory (by
      funext K
      exact propext (hX K).symm)
  let eY : (P Y).FullSubcategory ≌ (Q Y).FullSubcategory :=
    (E Y).fixedDerived.congrFullSubcategory (by
      funext K
      exact propext (hY K).symm)
  let F := rightDerivedLowerShriekOfCompactification
    (FiniteDiscreteOrdinary.coefficient A) c.obj.obj
  obtain ⟨cf⟩ := hcomp X Y f c.obj.obj
  obtain ⟨hOrd, ROrd, ⟨aOrd⟩, ⟨eROrd⟩⟩ := ordinary_small_adjunction A k
    (Y ↘ Spec (.of k)) f c.obj.obj
  have hF (K) (hK : P X K) : P Y (F.obj K) :=
    (hY _).mpr ((Q Y).prop_of_iso (cf.app K).symm (hOrd _ ((hX K).mp hK)))
  let L := (P Y).lift ((P X).ι ⋙ F) (fun M ↦ hF M.obj M.property)
  let LOrd := (Q Y).lift ((Q X).ι ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.obj.obj)
      (fun M ↦ hOrd M.obj M.property)
  have comm : L ⋙ eY.functor ≅ eX.functor ⋙ LOrd :=
    ((Q Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (P X).ι cf)
  let R := eY.functor ⋙ ROrd ⋙ eX.inverse
  have ae : (eX.functor ⋙ LOrd) ⋙ eY.inverse ⊣ R :=
    (eX.toAdjunction.comp aOrd).comp eY.symm.toAdjunction
  have el : (eX.functor ⋙ LOrd) ⋙ eY.inverse ≅ L :=
    Functor.isoWhiskerRight comm.symm eY.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L eY.unitIso.symm ≪≫ Functor.rightUnitor L
  have a : L ⊣ R := ae.ofNatIsoLeft el
  have hIso : (P X).IsClosedUnderIsomorphisms := ⟨fun e hK ↦
    (hX _).mpr ((Q X).prop_of_iso ((E X).fixedDerived.functor.mapIso e) ((hX _).mp hK))⟩
  have hShift : (P X).IsStableUnderShift ℤ := by
    refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
    exact (hX _).mpr ((Q X).prop_of_iso
      (((E X).fixedDerived.functor.commShiftIso n).app K).symm
      (((hX K).mp hK).shift n))
  let iP : (P X).FullSubcategory ⥤
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK _ _ hgen ↦ hgen K hK)
  let iQ : (P Y).FullSubcategory ⥤
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK _ _ hgen ↦ hgen K hK)
  have hG (K : (P Y).FullSubcategory) : P X (G.obj (iQ.obj K)).obj :=
    AdjunctionTransfer.rightAdjoint_preserves_generators (P X) (P Y) F hF h R a G adj K
  let Rs := (P X).lift
    (iQ ⋙ G ⋙ (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).ι) hG
  have asmall : L ⊣ Rs := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (fun K hK _ _ hgen ↦ hgen K hK))
    (ObjectProperty.fullyFaithfulιOfLE (fun K hK _ _ hgen ↦ hgen K hK))
    (Iso.refl _) (Iso.refl _)
  have eg : iQ ⋙ G ⋙
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).ι ≅
      R ⋙ (P X).ι :=
    Functor.isoWhiskerRight (a.rightAdjointUniq asmall).symm (P X).ι
  have eo : R ⋙ (P X).ι ⋙ (E X).fixedDerived.functor ≅
      eY.functor ⋙ (Q Y).ι ⋙
        ProEtale.rightDerivedUpperShriek (ULift.{u + 1} A) f :=
    Functor.isoWhiskerLeft (eY.functor ⋙ ROrd)
      (Functor.isoWhiskerRight eX.counitIso (Q X).ι) ≪≫
      Functor.isoWhiskerLeft eY.functor eROrd
  let S : ObjectProperty
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).FullSubcategory :=
    fun K ↦ P Y K.obj
  let V : S.FullSubcategory ⥤ (P Y).FullSubcategory :=
    (P Y).lift (S.ι ⋙
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).ι)
      (fun K ↦ K.property)
  have eg' : S.ι ⋙ G ⋙
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).ι ⋙
        (E X).fixedDerived.functor ≅
      V ⋙ eY.functor ⋙ (Q Y).ι ⋙
        ProEtale.rightDerivedUpperShriek (ULift.{u + 1} A) f :=
    Functor.isoWhiskerLeft V (Functor.isoWhiskerRight eg (E X).fixedDerived.functor ≪≫ eo)
  have hpos : 0 < ℓ ^ r := pow_pos (Fact.out : ℓ.Prime).pos _
  have hℓ : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k) (Fact.out : ℓ.Prime)
      (Fact.out : ringChar k ≠ ℓ)
  have hInvY : ∀ y : Y, IsUnit ((ℓ ^ r : ℕ) : Y.presheaf.stalk y) := by
    intro y
    have hu : IsUnit ((ℓ ^ r : ℕ) : Γ(Y, ⊤)) := by
      simpa using ((isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
        (Scheme.ΓSpecIso (.of k)).inv.hom).map
          (Y ↘ Spec (.of k)).appTop.hom
    simpa using hu.map (Y.presheaf.germ ⊤ y (by trivial)).hom
  let B := ULift.{u + 1} A
  let C := ModuleCat.{u + 1} B
  have : HasInvertibleExponent B X := HasInvertibleExponent.of_hom f
  obtain ⟨⟨L, ⟨eL⟩, CL, hL⟩, _⟩ :=
    Etale.smooth_tensor_duality B (ℓ ^ r) hpos hAr hInvY f d
  obtain ⟨⟨CT, hT⟩, _⟩ :=
    finite_etale_torsion_twist_line X (ℓ ^ r) hpos (fun x ↦ by
      have hu : IsUnit ((ℓ ^ r : ℕ) : Γ(Y, ⊤)) := by
        simpa using ((isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
          (Scheme.ΓSpecIso (.of k)).inv.hom).map
            (Y ↘ Spec (.of k)).appTop.hom
      simpa using (hu.map f.appTop.hom).map (X.presheaf.germ ⊤ x (by trivial)).hom)
      B hAr d
  let cover := CL.bind (fun i ↦ CT.pullback₁ (CL.f i))
  refine ⟨cover, ?_⟩
  intro i
  let j := cover.f i
  have Ltriv : (Etale.upperStar C j).obj L ≅
      MonoidalCategoryStruct.tensorUnit (Sheaf (cover.X i).smallEtaleTopology C) :=
    trivializationPullback B L (CL.f i.1) (pullback.fst (CL.f i.1) (CT.f i.2))
      (overTrivialization B L CL i.1 (hL i.1).some)
  let T := finiteEtaleTateTwist X (ℓ ^ r) B hAr d
  have Ttriv : (Etale.upperStar C j).obj T ≅
      MonoidalCategoryStruct.tensorUnit (Sheaf (cover.X i).smallEtaleTopology C) := by
    have he := trivializationPullback B T (CT.f i.2)
      (pullback.snd (CL.f i.1) (CT.f i.2))
      (overTrivialization B T CT i.2 (hT i.2).some)
    change (Etale.upperStar C
      (pullback.fst (CL.f i.1) (CT.f i.2) ≫ CL.f i.1)).obj T ≅ _
    rw [pullback.condition]
    exact he
  constructor
  · exact ⟨((comparisonUpperStarCompUpperStarIso C j).app T) ≪≫
      (comparisonUpperStar C (cover.X i)).mapIso Ttriv ≪≫
      (comparisonUpperStarConstantSheafIso B (cover.X i)).app (ModuleCat.of B B)⟩
  · let W := Etale.dualizingComplex B f
    have eW : W ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ⟦2 * (d : ℤ)⟧ :=
      (shiftEquiv' _ (-(2 * (d : ℤ))) (2 * (d : ℤ)) (neg_add_cancel _)).unitIso.app W ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso eL
    have wj : (Etale.upperStar C j).leftDerivedFunctor.obj W ≅
        (MonoidalCategoryStruct.tensorUnit
          (_root_.DerivedCategory (Sheaf (cover.X i).smallEtaleTopology C)))
            ⟦2 * (d : ℤ)⟧ :=
      (Etale.upperStar C j).leftDerivedFunctor.mapIso eW ≪≫
        Etale.IsShiftedRankOneLocalSystem.leftDerivedUpperStarShiftSingleIso j L (2 * (d : ℤ)) ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          ((_root_.DerivedCategory.singleFunctor _ 0).mapIso Ltriv ≪≫
            Etale.singleFunctorObjUnitIso C (cover.X i))
    let I := S.ι ⋙
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).ι
    let Rg := S.ι ⋙ G ⋙
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).ι
    let H := V ⋙ eY.functor
    have ev : I ⋙ (E Y).fixedDerived.functor ≅ H ⋙ (Q Y).ι := by
      dsimp only [I, H, V, eY, Equivalence.congrFullSubcategory]
      exact Iso.refl _
    have eo : (H ⋙ (Q Y).ι ⋙ ProEtale.rightDerivedUpperShriek B f) ⋙
        (ProEtale.upperStar C j).mapDerivedCategory ≅
      I ⋙ (E Y).fixedDerived.functor ⋙ (ProEtale.upperStar C f).mapDerivedCategory ⋙
        (ProEtale.upperStar C j).mapDerivedCategory ⋙ shiftFunctor _ (2 * (d : ℤ)) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft H (ordinarySmoothLocalIso A f d j wj) ≪≫
        (Functor.associator H (Q Y).ι _).symm ≪≫
        Functor.isoWhiskerRight ev.symm _ ≪≫ Functor.associator I _ _
    let Fm := (upperStar (FiniteDiscreteOrdinary.coefficient A) f).mapDerivedCategory
    let Jm := (upperStar (FiniteDiscreteOrdinary.coefficient A) j).mapDerivedCategory
    let Sm := shiftFunctor
      (_root_.DerivedCategory (FiniteDiscreteOrdinary.Internal A (cover.X i))) (2 * (d : ℤ))
    let Fo := (ProEtale.upperStar C f).mapDerivedCategory
    let Jo := (ProEtale.upperStar C j).mapDerivedCategory
    let So := shiftFunctor (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (cover.X i)) C)) (2 * (d : ℤ))
    have result : Rg ⋙ Jm ≅ I ⋙ Fm ⋙ Jm ⋙ Sm :=
      transportLocalFormula I Rg Fm Jm Sm
        (E Y).fixedDerived (E X).fixedDerived (E (cover.X i)).fixedDerived
        (H ⋙ (Q Y).ι ⋙ ProEtale.rightDerivedUpperShriek B f) Fo Jo So eg'
        (encodingPullbackIso A f (E Y) (E X))
        (encodingPullbackIso A j (E X) (E (cover.X i)))
        ((E (cover.X i)).fixedDerived.functor.commShiftIso (2 * (d : ℤ))) eo
    let finalIso := reassociateLocalFormula S.ι G
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).ι
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).ι
      Fm Jm Sm result
    exact ⟨by simpa only [S, P, Fm, Jm, Sm, FiniteDiscreteOrdinary.Internal,
      FiniteDiscreteOrdinary.coefficient] using finalIso⟩

set_option maxHeartbeats 400000 in
-- The per-ring `Rf^!` of upstream PR #1694 makes the final transport heavier.
end AlgebraicGeometry.ProEtale.CondensedRing
