/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedHomShiftUncurry
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Unsigned target shifts and derived evaluation

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08J7, Tags 08J9 and 08JC
(blueprint: lem-sf-ringed-hom-target-shift-evaluation).

The target Hom shift is the existing uniquely normalized unsigned shift. The tensor
shift below is uniquely specified by the unsigned first-factor total-tensor shift,
using the given closed symmetric structure's recorded K-flat comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.Functor SheafOfModules

namespace CategoryTheory.RingedHomTargetShift

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- Mathlib's unsigned first-factor shift, on the recorded total tensor itself.
Source: Stacks 0A8X and 06YN; Mathlib `mapBifunctorShift₁Iso`
(blueprint: lem-sf-ringed-hom-target-shift-evaluation). -/
def totalShift (P Q : RingedHomUniverses.Complex.{c, v, u} J R) (n : ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj (P⟦n⟧, Q) ≅
      ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q))⟦n⟧ :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  CochainComplex.mapBifunctorShift₁Iso P Q (MonoidalCategory.curriedTensor _) n

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
  (T : CoefficientTensorModels.{u, c, v, w} J R S)
  (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
    _ S.monoidal)
  (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)

private def flatPairWhiskering
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (PC : ObjectProperty (CochainComplex A ℤ))
    (P : ObjectProperty (HomotopyCategory A (.up ℤ)))
    (hP : ∀ X, P X ↔ PC X.as)
    (hL : (P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ _)).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι))
    (E : Type*) [Category E] :
    ((Functor.whiskeringLeft _ _ E).obj
      ((PC.ι ⋙ DerivedCategory.Q).prod (PC.ι ⋙ DerivedCategory.Q))).FullyFaithful := by
  let H := HomotopyCategory.quotient A (.up ℤ)
  let Qh := DerivedCategory.Qh (C := A)
  let I : PC.FullSubcategory ⥤ P.FullSubcategory :=
    { obj := fun p ↦ ⟨H.obj p.obj, (hP _).2 p.property⟩
      map := fun f ↦ ObjectProperty.homMk (H.map f.hom)
      map_id := by intro p; ext; exact H.map_id p.obj
      map_comp := by intro p q r f g; ext; exact H.map_comp f.hom g.hom }
  let L := P.ι ⋙ Qh
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  have : L.IsLocalization V := hL
  let ffI : ((Functor.whiskeringLeft _ _ E).obj (I.prod I)).FullyFaithful :=
    { preimage := fun {F G} τ ↦
        { app := fun X ↦ τ.app
            (⟨X.1.obj.as, (hP _).1 X.1.property⟩,
              ⟨X.2.obj.as, (hP _).1 X.2.property⟩)
          naturality := by
            intro X Y f
            let Xc : PC.FullSubcategory × PC.FullSubcategory :=
              (⟨X.1.obj.as, (hP _).1 X.1.property⟩,
                ⟨X.2.obj.as, (hP _).1 X.2.property⟩)
            let Yc : PC.FullSubcategory × PC.FullSubcategory :=
              (⟨Y.1.obj.as, (hP _).1 Y.1.property⟩,
                ⟨Y.2.obj.as, (hP _).1 Y.2.property⟩)
            let f' : Xc ⟶ Yc :=
              (ObjectProperty.homMk f.1.hom.out, ObjectProperty.homMk f.2.hom.out)
            have hm : (I.prod I).map f' = f := by
              ext <;> exact HomotopyCategory.quotient_map_out _
            have h := τ.naturality f'
            change F.map ((I.prod I).map f') ≫ τ.app Yc =
              τ.app Xc ≫ G.map ((I.prod I).map f') at h
            rw [hm] at h
            exact h }
      map_preimage := by intros; ext X; rfl
      preimage_map := by intros; ext X; rfl }
  let ffL := Localization.fullyFaithfulWhiskeringLeft (L.prod L) (V.prod V) E
  let ff := ffL.comp ffI
  let a : I ⋙ L ≅ PC.ι ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft PC.ι (DerivedCategory.quotientCompQhIso A)
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso (NatIso.prod a a))

private theorem resolvingLocalization :
    ((tensorDescentClass.{c, v, max c v u, w} (R := R)).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage
        (tensorDescentClass.{c, v, max c v u, w} (R := R)).ι) := by
  unfold tensorDescentClass
  let d := site_derived_tensor_descent_independentCoefficients.{c, v, max c v u, w, 0, 0} J R
  let V := (HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage d.choose.ι
  let F := d.choose_spec.2.1.choose
  have : F.IsEquivalence := d.choose_spec.2.1.choose_spec.1
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V d.choose_spec.2.1.choose_spec.2.some

private abbrev flatProperty : ObjectProperty (RingedHomUniverses.Complex.{c, v, u} J R) :=
  TensorFlatRepresentative (J := J) (R := R)

private def publishedComparison :
    ((flatProperty.{c, v, u} J R).ι.prod (flatProperty.{c, v, u} J R).ι) ⋙
        coefficientTotalTensor.{u, c, v} J R ⋙ DerivedCategory.Q ≅
      (((flatProperty.{c, v, u} J R).ι ⋙ DerivedCategory.Q).prod
        ((flatProperty.{c, v, u} J R).ι ⋙ DerivedCategory.Q)) ⋙
          SheafOfModules.siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R := by
  let d := site_derived_tensor_descent_independentCoefficients.{c, v, max c v u, w, 0, 0} J R
  let H := HomotopyCategory.quotient (RingedTensorModules.{c, v, u} J R) (.up ℤ)
  let I : (flatProperty.{c, v, u} J R).FullSubcategory ⥤ d.choose.FullSubcategory :=
    { obj := fun X ↦ ⟨H.obj X.obj, (d.choose_spec.1 _).2 X.property⟩
      map := fun f ↦ ObjectProperty.homMk (H.map f.hom)
      map_id := by intro X; ext; exact H.map_id _
      map_comp := by intro X Y Z f g; ext; exact H.map_comp _ _ }
  let a := Functor.isoWhiskerLeft (flatProperty.{c, v, u} J R).ι
    (DerivedCategory.quotientCompQhIso (RingedTensorModules.{c, v, u} J R))
  exact Functor.isoWhiskerLeft
      (((flatProperty.{c, v, u} J R).ι.prod (flatProperty.{c, v, u} J R).ι) ⋙
        coefficientTotalTensor.{u, c, v} J R)
      (DerivedCategory.quotientCompQhIso (RingedTensorModules.{c, v, u} J R)).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      ((flatProperty.{c, v, u} J R).ι.prod (flatProperty.{c, v, u} J R).ι)
      (tensorDescentComplexIso (R := R)).symm) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (I.prod I) (tensorDescentDerivedIso (R := R)) ≪≫
    Functor.isoWhiskerRight (NatIso.prod a a)
      (siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R)

private theorem publishedComparison_app
    (A B : RingedHomUniverses.Complex.{c, v, u} J R)
    (hA : TensorFlatRepresentative (J := J) (R := R) A)
    (hB : TensorFlatRepresentative (J := J) (R := R) B) :
    (publishedComparison.{c, v, u, w} J R).app (⟨A, hA⟩, ⟨B, hB⟩) =
      tensorDescentPair (J := J) (R := R) A B hA hB := by
  rfl

/-- Representative characterization of the canonical first-factor tensor shift.
The two paths start at Q(Tot(P[n] tensor Q)); all comparisons are the fixed ones.
Only flat-term K-flat test representatives occur; the derived inputs are unrestricted.
Source: Stacks 06YU, 0A8X; tensor-shift descent
(blueprint: lem-sf-ringed-hom-target-shift-evaluation). -/
def TensorShiftModel
    (l : ∀ n : ℤ,
      (shiftFunctor (RingedHomUniverses.D.{c, v, u, w} J R) n).prod (𝟭 _) ⋙ S.tensor ≅
        S.tensor ⋙ shiftFunctor _ n) : Prop :=
  ∀ (P Q : RingedHomUniverses.Complex.{c, v, u} J R)
    (hP : TensorFlatRepresentative (J := J) (R := R) P)
    (hQ : TensorFlatRepresentative (J := J) (R := R) Q) (n : ℤ),
    (hc.tensorIso (P⟦n⟧) Q (Or.inr hQ.1)).hom ≫
        S.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P)
          (𝟙 (DerivedCategory.Q.obj Q))) ≫
        (l n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (totalShift.{c, v, u} J R P Q n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≫
        ((hc.tensorIso P Q (Or.inl hP.1)).hom)⟦n⟧'

private def firstShiftIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int] (n : ℤ) :
    (shiftFunctor D n).prod (𝟭 D) ⋙ uncurry.obj T ≅
      uncurry.obj T ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun X ↦ ((T.flip.obj X.2).commShiftIso n).app X.1) (by
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
    change ((T.map (f₁⟦n⟧')).app X₂ ≫ (T.obj (Y₁⟦n⟧)).map f₂) ≫
        ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ =
      ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫
        ((T.map f₁).app X₂ ≫ (T.obj Y₁).map f₂)⟦n⟧'
    have hh := NatTrans.shift_app_comm (T.flip.map f₂) n Y₁
    change ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ ≫
      ((T.obj Y₁).map f₂)⟦n⟧' = (T.obj (Y₁⟦n⟧)).map f₂ ≫
        ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ at hh
    have h₁ := (T.flip.obj X₂).commShiftIso_hom_naturality f₁ n
    change (T.map (f₁⟦n⟧')).app X₂ ≫
        ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ =
      ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫
        ((T.map f₁).app X₂)⟦n⟧' at h₁
    rw [Category.assoc, ← hh, ← Category.assoc, h₁, Category.assoc,
      CategoryTheory.Functor.map_comp])

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem flatShift (A : RingedHomUniverses.Complex.{c, v, u} J R)
    (hA : TensorFlatRepresentative (J := J) (R := R) A) (n : ℤ) :
    TensorFlatRepresentative (J := J) (R := R) (A⟦n⟧) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  refine ⟨?_, fun i ↦ hA.2 (i + n)⟩
  intro F hF
  have ht := hA.1 F hF
  have hs : (CochainComplex.mapBifunctor F A (MonoidalCategory.curriedTensor _)⟦n⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (RingedTensorModules.{c, v, u} J R)).le_shift
      n _ ht
  intro i
  exact (hs i).of_iso (CochainComplex.mapBifunctorShift₂Iso F A
    (MonoidalCategory.curriedTensor _) n).symm

private def transportShift
    {D : Type*} [Category D] [HasShift D ℤ]
    {U V : D × D ⥤ D} (e : U ≅ V) (n : ℤ)
    (l : (shiftFunctor D n).prod (𝟭 _) ⋙ U ≅ U ⋙ shiftFunctor D n) :
    (shiftFunctor D n).prod (𝟭 _) ⋙ V ≅ V ⋙ shiftFunctor D n :=
  isoWhiskerLeft ((shiftFunctor D n).prod (𝟭 _)) e.symm ≪≫ l ≪≫
    isoWhiskerRight e (shiftFunctor D n)

private theorem transportShift_square
    {D : Type*} [Category D] [HasShift D ℤ]
    {U V : D × D ⥤ D} (e : U ≅ V) (n : ℤ)
    (l : (shiftFunctor D n).prod (𝟭 _) ⋙ U ≅ U ⋙ shiftFunctor D n)
    (P P' Q X Y : D) (t : P' ⟶ P⟦n⟧)
    (c' : X ⟶ U.obj (P', Q)) (c : Y ⟶ U.obj (P, Q))
    (d' : X ⟶ V.obj (P', Q)) (d : Y ⟶ V.obj (P, Q))
    (g : X ⟶ Y⟦n⟧)
    (hc' : c' ≫ e.hom.app (P', Q) = d')
    (hc : c ≫ e.hom.app (P, Q) = d)
    (h : c' ≫ U.map (Prod.mkHom t (𝟙 Q)) ≫ l.hom.app (P, Q) = g ≫ c⟦n⟧') :
    d' ≫ V.map (Prod.mkHom t (𝟙 Q)) ≫ (transportShift e n l).hom.app (P, Q) =
      g ≫ d⟦n⟧' := by
  dsimp only [transportShift, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.prod_obj, Functor.id_obj]
  calc
    _ = (c' ≫ U.map (Prod.mkHom t (𝟙 Q)) ≫ l.hom.app (P, Q)) ≫
        (e.hom.app (P, Q))⟦n⟧' := by
      rw [← hc']
      simp only [Category.assoc, ← e.hom.naturality_assoc (Prod.mkHom t (𝟙 Q)),
        Iso.hom_inv_id_app_assoc]
    _ = (g ≫ c⟦n⟧') ≫ (e.hom.app (P, Q))⟦n⟧' := by rw [h]
    _ = _ := by rw [Category.assoc, ← Functor.map_comp, hc]

private theorem flatRepresentatives (M : RingedHomUniverses.D.{c, v, u, w} J R) :
    ∃ P, TensorFlatRepresentative (J := J) (R := R) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let Q : RingedHomUniverses.Complex.{c, v, u} J R ⥤
      RingedHomUniverses.D.{c, v, u, w} J R := DerivedCategory.Q
  obtain ⟨P, f, hP, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage M)
  have : QuasiIso f := hf
  refine ⟨P, ⟨hP, ?_⟩, ⟨asIso (Q.map f) ≪≫ Q.objObjPreimageIso M⟩⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso R (P.X i)).symm (hflat i)

private theorem tensorShiftModel_unique
    (l l' : ∀ n : ℤ,
      (shiftFunctor (RingedHomUniverses.D.{c, v, u, w} J R) n).prod (𝟭 _) ⋙ S.tensor ≅
        S.tensor ⋙ shiftFunctor _ n)
    (hl : TensorShiftModel.{c, v, u, w} J R S T β hc l)
    (hl' : TensorShiftModel.{c, v, u, w} J R S T β hc l') : l = l' := by
  funext n
  apply Iso.ext
  apply NatTrans.ext
  funext ⟨M, N⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := flatRepresentatives.{c, v, u, w} J R M
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := flatRepresentatives.{c, v, u, w} J R N
  have h : (l n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (l' n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    have hh := (hl P Q hP hQ n).trans (hl' P Q hP hQ n).symm
    have : IsIso (S.tensor.map (Prod.mkHom
        ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 (DerivedCategory.Q.obj Q)))) := by
      change IsIso ((S.tensor.mapIso
        (((DerivedCategory.Q.commShiftIso n).app P).prod (Iso.refl _))).hom)
      infer_instance
    exact (cancel_epi ((hc.tensorIso (P⟦n⟧) Q (Or.inr hQ.1)).hom ≫
      S.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P)
        (𝟙 (DerivedCategory.Q.obj Q))))).mp (by simpa only [Category.assoc] using hh)
  let e := eP.prod eQ
  apply (cancel_epi (((shiftFunctor _ n).prod (𝟭 _) ⋙ S.tensor).map e.hom)).mp
  rw [(l n).hom.naturality, (l' n).hom.naturality, h]

section
attribute [local irreducible] SheafOfModules.monoidalCategory

set_option maxHeartbeats 2000000 in
-- Comparing the nested localized tensor functors needs additional elaboration heartbeats.
/-- The first-factor tensor shift is determined by unsigned reindexing on K-flats.
Source: Stacks 06YU, 0A8X; the descent step in the node's proof
(blueprint: lem-sf-ringed-hom-target-shift-evaluation).

Proof: a shift of a flat-term K-flat complex is flat-term K-flat: tensor with an
acyclic complex, use the second-factor signed total shift, and shift the resulting
acyclic total complex. Apply lem-weil-pbc-derived-tensor-shift-descent. Compare its
published tensor with S.tensor by the arbitrary-transformation extension clause of
lem-weil-pbc-site-derived-tensor-descent, using hc.tensorIso and hc.tensorIso_both.
Transport the first-factor shift across this natural isomorphism. Its representative
square is the displayed equation, since hc.tensorIso_naturality identifies the fixed
comparisons. Uniqueness follows from the same extension clause: resolving pairs
are essentially surjective after localization, so natural transformations agreeing
on those pairs agree on every derived pair. This applies separately to every n. -/
theorem tensorShift_existsUnique :
    ∃! l : (∀ n : ℤ,
      (shiftFunctor (RingedHomUniverses.D.{c, v, u, w} J R) n).prod (𝟭 _) ⋙ S.tensor ≅
        S.tensor ⋙ shiftFunctor _ n),
      TensorShiftModel.{c, v, u, w} J R S T β hc l := by
  classical
  let PC := flatProperty.{c, v, u} J R
  let P := tensorDescentClass.{c, v, max c v u, w} (R := R)
  let d := site_derived_tensor_descent_independentCoefficients.{c, v, max c v u, w, 0, 0} J R
  let L := (PC.ι ⋙ DerivedCategory.Q).prod (PC.ι ⋙ DerivedCategory.Q)
  let U := siteDerivedTensorIndependentCoefficients.{c, v, max c v u, w} J R
  let ff := flatPairWhiskering PC P d.choose_spec.1 (resolvingLocalization.{c, v, u, w} J R)
    (RingedHomUniverses.D.{c, v, u, w} J R)
  let I : PC.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)) :=
    ObjectProperty.lift _ PC.ι (fun X ↦ X.property.1)
  let e₀ : L ⋙ U ≅ L ⋙ S.tensor :=
    (publishedComparison.{c, v, u, w} J R).symm ≪≫ Functor.isoWhiskerLeft (I.prod I) T.comparison
  let e : U ≅ S.tensor := ff.preimageIso e₀
  have he (A B : RingedHomUniverses.Complex.{c, v, u} J R)
      (hA : TensorFlatRepresentative (J := J) (R := R) A)
      (hB : TensorFlatRepresentative (J := J) (R := R) B) :
      (tensorDescentPair (J := J) (R := R) A B hA hB).hom ≫
        e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
      (hc.tensorIso A B (Or.inl hA.1)).hom := by
    have hh := congr_app (ff.map_preimage e₀.hom) (⟨A, hA⟩, ⟨B, hB⟩)
    change e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
      e₀.hom.app (⟨A, hA⟩, ⟨B, hB⟩) at hh
    dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, whiskerLeft_app] at hh
    conv_rhs at hh =>
      arg 1
      rw [← Iso.app_inv, publishedComparison_app.{c, v, u, w} J R A B hA hB]
    have h : e.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
        (tensorDescentPair (J := J) (R := R) A B hA hB).inv ≫
          (T.iso J R S A B hA.1 hB.1).hom := hh
    rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      hc.tensorIso_both A B hA.1 hB.1]
  have stable : ∀ A : RingedHomUniverses.Complex.{c, v, u} J R,
      TensorFlatRepresentative (J := J) (R := R) A →
      ∀ n : ℤ, TensorFlatRepresentative (J := J) (R := R) (A⟦n⟧) := by
    intro A hA n
    exact flatShift.{c, v, u} J R A hA n
  obtain ⟨s, hs, _, _⟩ :=
    SheafOfModules.derived_tensor_shift_descent (J := J) (R := R) stable
  let := s
  let l₀ (n : ℤ) : (shiftFunctor _ n).prod (𝟭 _) ⋙ U ≅ U ⋙ shiftFunctor _ n :=
    Functor.isoWhiskerLeft ((shiftFunctor _ n).prod (𝟭 _))
        (Functor.currying.counitIso.app U).symm ≪≫
      firstShiftIso (Functor.curry.obj U) n ≪≫
        Functor.isoWhiskerRight (Functor.currying.counitIso.app U) (shiftFunctor _ n)
  let l (n : ℤ) := transportShift e n (l₀ n)
  have hl : TensorShiftModel.{c, v, u, w} J R S T β hc l := by
    intro A B hA hB n
    have hn := (hs A B hA hB n).1
    have he' := he (A⟦n⟧) B (stable A hA n) hB
    have heAB := he A B hA hB
    have hl₀ : (l₀ n).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
        (((siteRestrictionDerivedTensor (J := J) (R := R)).flip.obj
          (DerivedCategory.Q.obj B)).commShiftIso n).hom.app
            (DerivedCategory.Q.obj A) := by
      dsimp only [l₀, firstShiftIso, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.app_hom, Iso.app_inv,
        NatIso.ofComponents_hom_app,
        Functor.currying_counitIso_hom_app_app,
        Functor.currying_counitIso_inv_app_app]
      erw [Category.id_comp, Functor.map_id, Category.comp_id]
    conv_rhs => rw [← Category.assoc]
    apply transportShift_square e n (l₀ n)
      (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj (A⟦n⟧))
      (DerivedCategory.Q.obj B) _ _
      ((DerivedCategory.Q.commShiftIso n).hom.app A)
      (tensorDescentPair (J := J) (R := R) (A⟦n⟧) B (stable A hA n) hB).hom
      (tensorDescentPair (J := J) (R := R) A B hA hB).hom
      (hc.tensorIso (A⟦n⟧) B (Or.inr hB.1)).hom
      (hc.tensorIso A B (Or.inl hA.1)).hom _ he' heAB
    rw [hl₀]
    simpa only [U, siteRestrictionDerivedTensor, Functor.flip_obj_map,
      Functor.curry_obj_map_app, totalShift, RingedHomUniverses.Modules,
      coefficientTotalTensor, tensorShiftTotal, ringedSiteModules,
      SheafOfModules.cochainModulesMonoidal, Functor.comp_obj, Functor.flip_obj_obj,
      Functor.curry_obj_obj_obj, Functor.uncurry_obj_obj,
      Functor.map₂HomologicalComplex_obj_obj, Category.assoc] using hn
  exact ⟨l, hl, fun l' hl' ↦ tensorShiftModel_unique.{c, v, u, w} J R S T β hc l' l hl' hl⟩

end

/-- The canonical tensor shift, selected from its unique representative characterization.
This is a unique object construction; no arbitrary comparison or resolution is chosen.
Source: Stacks 06YU, 0A8X
(blueprint: lem-sf-ringed-hom-target-shift-evaluation). -/
def tensorShift (n : ℤ) :
    (shiftFunctor (RingedHomUniverses.D.{c, v, u, w} J R) n).prod (𝟭 _) ⋙ S.tensor ≅
      S.tensor ⋙ shiftFunctor _ n :=
  (tensorShift_existsUnique.{c, v, u, w} J R S T β hc).exists.choose n

/-- Evaluation commutes with the canonical unsigned covariant Hom shift.
Source: Stacks 08JC, with the explicit 0A8X calculation (not a verbatim equation in 08JC)
(blueprint: lem-sf-ringed-hom-target-shift-evaluation).

Proof (the node's six steps):
1. Resolve K by a flat-term K-flat P and represent M by a K-injective I. Resolve
   B = Hom(P,I) by a flat-term K-flat A -> B (lem-pc-kflat-resolution). Use the
   fixed comparisons of def-pur-derived-internal-hom and
   def-coef-hom-representative-evaluation; I[n] remains K-injective.
2. Unsigned reindexing u : Hom(P,I[n]) -> Hom(P,I)[n] is a chain isomorphism:
   both differentials in degree r are (-1)^n d_I f - (-1)^r f d_P. If a : A -> B,
   put b = u.inv followed after a[n]. The normalized Hom shift sends gamma_n Qb
   to (gamma Qa)[n]. A[n] is again flat-term K-flat by the signed tensor shift.
3. The normalized tensor-Hom adjunction identifies the two evaluated composites
   with Q of psi(x tensor y) = a(x)(y) and psi_n(x tensor y) = b(x)(y), followed
   by the inverse localized augmentation. For I[n], compare through its fixed
   augmentation; lem-pur-rhom-well-defined makes its Hom map invertible, so it
   cancels. Target naturality then gives the evaluation into M[n].
4. On each summand and local pure tensor, psi_n = psi[n] followed after the
   unsigned first-factor tensor shift: both values are a^(r+n)(x)^q(y).
   No tensor is interchanged with the infinite Hom product.
5. Localize this chain equality. The representative characterization of tensorShift
   is precisely the conjugation by the native comparison and Q's shift comparison.
   Naturality moves gamma Qa across it; cancel the isomorphism gamma_n Qb tensored
   with the identity of K. This gives the equation below for arbitrary K,M,n.
6. The closed adjunction bijection is injective and its inverse is evaluation after
   tensoring. Thus this equation also characterizes the Hom shift as the right-adjoint
   shift for - tensor K. No boundedness, perfectness or cohomological flatness is used. -/
theorem evaluation_eq (K M : RingedHomUniverses.D.{c, v, u, w} J R) (n : ℤ) :
    S.evaluation K (M⟦n⟧) =
      S.tensor.map (Prod.mkHom
          (((RingedHomUniverses.hom.{c, v, u, w} J R K).commShiftIso n).hom.app M)
          (𝟙 K)) ≫
        (tensorShift.{c, v, u, w} J R S T β hc n).hom.app
          ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, M), K) ≫
        (S.evaluation K M)⟦n⟧' := by
  classical
  obtain ⟨P, I, A, eK, eM, u, a, hP, hA, hAn, hI, hIn, hu, hfn, hn⟩ :=
    RingedHomShift.exists_normalized_representatives.{c, v, u, w} J R K M n
  let f := DerivedCategory.Q.map a ≫
    RingedHomShift.comparison.{c, v, u, w} J R P I eK eM
  let eMn := RingedHomShift.shiftedIso.{c, v, u, w} J R eM n
  let b := a⟦n⟧' ≫ u.hom
  let fn := DerivedCategory.Q.map b ≫
    RingedHomShift.comparison.{c, v, u, w} J R P (I⟦n⟧) eK eMn
  let c₀ := (hc.tensorIso A P (Or.inl hA.1)).hom
  let cₙ := (hc.tensorIso (A⟦n⟧) P (Or.inr hP.1)).hom
  let qA := (DerivedCategory.Q.commShiftIso n).hom.app A
  let qT := (DerivedCategory.Q.commShiftIso n).hom.app
    ((coefficientTotalTensor.{u, c, v} J R).obj (A, P))
  let l := tensorShift.{c, v, u, w} J R S T β hc n
  obtain ⟨ψ, hψ, he⟩ := RingedHomShift.exists_evaluation_model.{c, v, u, w}
    J R S T β hc A P I hA.1 hP.1 eK eM a
  obtain ⟨ψn, hψn, hen⟩ := RingedHomShift.exists_evaluation_model.{c, v, u, w}
    J R S T β hc (A⟦n⟧) P (I⟦n⟧) hAn.1 hP.1 eK eMn b
  have hψshift := RingedHomShift.uncurry_shift.{c, v, u}
    J R A P I n u hu a ψ ψn hψ hψn
  change ψn = (totalShift.{c, v, u} J R A P n).hom ≫ ψ⟦n⟧' at hψshift
  have hl := (tensorShift_existsUnique.{c, v, u, w} J R S T β hc).exists.choose_spec
    A P hA hP n
  change cₙ ≫ S.tensor.map (Prod.mkHom qA (𝟙 _)) ≫ l.hom.app (_, _) =
    DerivedCategory.Q.map (totalShift.{c, v, u} J R A P n).hom ≫ qT ≫ c₀⟦n⟧' at hl
  change fn ≫ _ = qA ≫ f⟦n⟧' at hn
  change c₀ ≫ S.tensor.map (Prod.mkHom f eK.hom) ≫ S.evaluation K M =
    DerivedCategory.Q.map ψ ≫ eM.hom at he
  change cₙ ≫ S.tensor.map (Prod.mkHom fn eK.hom) ≫ S.evaluation K (M⟦n⟧) =
    DerivedCategory.Q.map ψn ≫ eMn.hom at hen
  have hnat := l.hom.naturality (Prod.mkHom f eK.hom)
  change S.tensor.map (Prod.mkHom (f⟦n⟧') eK.hom) ≫ l.hom.app (_, _) =
    l.hom.app (_, _) ≫ (S.tensor.map (Prod.mkHom f eK.hom))⟦n⟧' at hnat
  have hq := (DerivedCategory.Q.commShiftIso n).hom.naturality ψ
  change DerivedCategory.Q.map (ψ⟦n⟧') ≫
      (DerivedCategory.Q.commShiftIso n).hom.app I = qT ≫
      (DerivedCategory.Q.map ψ)⟦n⟧' at hq
  have hm (X Y Z : RingedHomUniverses.D.{c, v, u, w} J R)
      (X' Y' Z' : RingedHomUniverses.D.{c, v, u, w} J R)
      (g : X ⟶ Y) (h : Y ⟶ Z) (g' : X' ⟶ Y') (h' : Y' ⟶ Z') :
      S.tensor.map (Prod.mkHom g g') ≫ S.tensor.map (Prod.mkHom h h') =
        S.tensor.map (Prod.mkHom (g ≫ h) (g' ≫ h')) :=
    (S.tensor.map_comp (Prod.mkHom g g') (Prod.mkHom h h')).symm
  have hmaps : S.tensor.map (Prod.mkHom qA (𝟙 _)) ≫
      S.tensor.map (Prod.mkHom (f⟦n⟧') eK.hom) =
    S.tensor.map (Prod.mkHom fn eK.hom) ≫ S.tensor.map (Prod.mkHom
      (((RingedHomUniverses.hom.{c, v, u, w} J R K).commShiftIso n).hom.app M)
      (𝟙 K)) := by
    rw [hm, hm]
    simp only [Category.id_comp, Category.comp_id, hn]
  have : IsIso fn := hfn
  have : IsIso (S.tensor.map (Prod.mkHom fn eK.hom)) := by
    change IsIso ((S.tensor.mapIso ((asIso fn).prod eK)).hom)
    infer_instance
  have : IsIso cₙ := by dsimp only [cₙ]; infer_instance
  apply (cancel_epi (cₙ ≫ S.tensor.map (Prod.mkHom fn eK.hom))).1
  simp only [Category.assoc]
  rw [hen]
  calc
    DerivedCategory.Q.map ψn ≫ eMn.hom =
        DerivedCategory.Q.map (totalShift.{c, v, u} J R A P n).hom ≫
          qT ≫ (DerivedCategory.Q.map ψ ≫ eM.hom)⟦n⟧' := by
      rw [hψshift, Functor.map_comp]
      change (DerivedCategory.Q.map (totalShift.{c, v, u} J R A P n).hom ≫
        DerivedCategory.Q.map (ψ⟦n⟧')) ≫
          ((DerivedCategory.Q.commShiftIso n).hom.app I ≫ eM.hom⟦n⟧') = _
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hq]
    _ = DerivedCategory.Q.map (totalShift.{c, v, u} J R A P n).hom ≫
          qT ≫ (c₀ ≫ S.tensor.map (Prod.mkHom f eK.hom) ≫ S.evaluation K M)⟦n⟧' := by
      rw [he]
    _ = cₙ ≫ S.tensor.map (Prod.mkHom qA (𝟙 _)) ≫ l.hom.app (_, _) ≫
          (S.tensor.map (Prod.mkHom f eK.hom))⟦n⟧' ≫ (S.evaluation K M)⟦n⟧' := by
      simpa only [Functor.map_comp, Category.assoc] using
        (congrArg (fun z ↦ z ≫ (S.tensor.map (Prod.mkHom f eK.hom))⟦n⟧' ≫
          (S.evaluation K M)⟦n⟧') hl).symm
    _ = cₙ ≫ S.tensor.map (Prod.mkHom fn eK.hom) ≫
          S.tensor.map (Prod.mkHom
            (((RingedHomUniverses.hom.{c, v, u, w} J R K).commShiftIso n).hom.app M)
            (𝟙 K)) ≫ l.hom.app (_, _) ≫ (S.evaluation K M)⟦n⟧' := by
      rw [← reassoc_of% hnat]
      simpa only [Category.assoc, RingedHomUniverses.hom, Functor.curry_obj_obj_obj] using
        congrArg (fun z ↦ cₙ ≫ z ≫ l.hom.app (_, _) ≫
          (S.evaluation K M)⟦n⟧') hmaps


end CategoryTheory.RingedHomTargetShift
