/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteBaseChangeRestrictionCoherence
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorRestrictionCoherence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorDerivedComparison
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorOrdinaryComparison
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorTotalOfOrdinary
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorSupportAux
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.CategoryTheory.Derived.DerivedCoefficientMapDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-!
# Normalized open extension, tensor and base change

Construct the site square and tensor models explicitly. Open-support results make
the adjunction transposes invertible; their adjunct equations then determine both
restriction formulas. Source: Stacks 03DI, 0F6Z, 0E8I and 0GL1
(blueprint: lem-sf-open-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v h w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem ordinaryUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Mod (restrictRing m j R)) :
    IsIso (o.adjunction.unit.app M) := by
  have h : o.adjunction.unit.app M = (o.sectionIso M).inv := by
    apply (cancel_mono (o.sectionIso M).hom).1
    rw [o.sectionUnit, Iso.inv_hom_id]
    rfl
  rw [h]
  infer_instance

private theorem derivedUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Der (restrictRing m j R)) :
    IsIso ((exactDerivedAdjunction o.adjunction).unit.app M) := by
  let a := exactDerivedAdjunction o.adjunction
  have hQ (P : CochainComplex (Mod (restrictRing m j R)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ,
          IsIso (((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ ordinaryUnit_isIso o (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (restrict m j R).mapDerivedCategoryFactors.inv.app _ ≫
            (restrict m j R).mapDerivedCategory.map
              (o.ordinary.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, exactDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

private def transposeNatural
    {A B E : Type*} [Category A] [Category B] [Category E]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) {P : E ⥤ A} {Q : E ⥤ B}
    (t : P ⟶ Q ⋙ G) : P ⋙ F ⟶ Q where
  app X := (a.homEquiv _ _).symm (t.app X)
  naturality _X _Y f := a.homEquiv_naturality_right_square _ _ _ _ (t.naturality f)

private theorem isIso_of_adjunct
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) [IsIso a.unit] {X : B} {Y : A} (f : F.obj Y ⟶ X)
    (hf : IsIso (a.homEquiv _ _ f)) (hs : F.essImage X) : IsIso f := by
  have : F.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : F.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (a.counit.app X) := a.isIso_counit_app_iff_mem_essImage.mpr hs
  have := hf
  have he : f = F.map (a.homEquiv _ _ f) ≫ a.counit.app X := by
    exact ((a.homEquiv _ _).symm_apply_apply f).symm
  rw [he]
  infer_instance

private theorem tensorModel_exists {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) :
    Nonempty (TensorModel R) := by
  let A := Mod R
  let H := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨P, hp, hloc, ⟨B, ⟨hB⟩, T, ⟨hT⟩⟩, hd⟩ :=
    site_derived_tensor_descent_independentCoefficients.{u + 1, u, u + 1, u + 2, 0, 0} J R
  let f : (resolving R).FullSubcategory ⥤ P.FullSubcategory :=
    P.lift ((resolving R).ι ⋙ H) (fun X ↦ (hp _).2 X.property)
  let e : (resolving R).ι ⋙ H ⋙ DerivedCategory.Qh ≅
      (resolving R).ι ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (resolving R).ι (DerivedCategory.quotientCompQhIso A)
  let rep : ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q ≅
      (((resolving R).ι ⋙ DerivedCategory.Q).prod
        ((resolving R).ι ⋙ DerivedCategory.Q)) ⋙ T :=
    Functor.isoWhiskerLeft (((resolving R).ι.prod (resolving R).ι) ⋙ total R)
        (DerivedCategory.quotientCompQhIso A).symm ≪≫
      Functor.isoWhiskerLeft ((resolving R).ι.prod (resolving R).ι)
        (Functor.isoWhiskerRight hB.symm DerivedCategory.Qh) ≪≫
      Functor.isoWhiskerLeft (f.prod f) hT ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) T
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X),
        HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, q, hK, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hs : ∀ n, IsFlatOnSite (J := J) (R := R) (K.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (K.X n)).symm (hf n)
    refine ⟨⟨H.obj K, (hp _).2 ⟨hK, hs⟩⟩, H.map q, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering (Der R) H
    (HomotopyCategory.quotient_obj_surjective) (HomotopyCategory.quasiIso A (.up ℤ))
    DerivedCategory.Qh (resolving R) P (fun X ↦ (hp _).symm) hres
  exact ⟨{ preadditive := tensorPreadditive R
           functor := T
           representative := rep
           descent := fun F G ↦ ff.map_bijective F G }⟩

end SheafOfModules.OpenTensorNormalization

namespace SheafOfModules
open OpenTensorNormalization

end SheafOfModules
