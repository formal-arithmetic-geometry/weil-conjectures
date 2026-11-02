/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
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
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction

/-! # Etale to pro-etale comparison preserves signed symmetry

Source: Stacks Project, Cohomology on Sites, Tag 07A4
(blueprint: lem-pur-comparison-tensorator-signed-symmetry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

private theorem transport_braiding
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {L V : C ⥤ D} (e : L ≅ V)
    (δ : ∀ A B, L.obj (A ⊗ B) ⟶ L.obj A ⊗ L.obj B)
    (hδ : ∀ A B, L.map (β_ A B).hom ≫ δ B A =
      δ A B ≫ (β_ (L.obj A) (L.obj B)).hom) (A B : C) :
    V.map (β_ A B).hom ≫ e.inv.app (B ⊗ A) ≫ δ B A ≫
        (e.hom.app B ⊗ₘ e.hom.app A) =
      e.inv.app (A ⊗ B) ≫ δ A B ≫ (e.hom.app A ⊗ₘ e.hom.app B) ≫
        (β_ (V.obj A) (V.obj B)).hom := by
  rw [e.inv.naturality_assoc, reassoc_of% hδ A B]
  rw [BraidedCategory.braiding_naturality]

private theorem transport_tensor_hom
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L V : C ⥤ D} (e : L ≅ V)
    (δ : ∀ J, (curriedTensor C).obj J ⋙ L ≅ L ⋙ (curriedTensor D).obj (L.obj J))
    (J K : C) :
    ((Functor.isoWhiskerLeft _ e.symm ≪≫ δ J ≪≫
      Functor.isoWhiskerRight e _ ≪≫
      Functor.isoWhiskerLeft V ((curriedTensor D).mapIso (e.app J))).hom.app K) =
      e.inv.app (J ⊗ K) ≫ (δ J).hom.app K ≫
        (e.hom.app J ⊗ₘ e.hom.app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    curriedTensor_obj_map, curriedTensor_map_app, curriedTensor_obj_obj,
    MonoidalCategory.tensorHom_def']

private theorem adjunction_delta_braiding
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [iG : G.LaxMonoidal] (adj : F ⊣ G)
    (hG : ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)
    (X Y : C) :
    letI := adj.leftAdjointOplaxMonoidal
    F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  let : G.LaxBraided := { toLaxMonoidal := iG, braided := hG }
  exact (Adjunction.leftAdjointOplaxMonoidal_δ_braiding adj X Y).symm

private theorem derived_comparison_tensor (J K : _root_.DerivedCategory C) :
    ((Functor.isoWhiskerLeft _ F.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (asIso F.leftDerivedTensorComparison).app J ≪≫
      Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory ((curriedTensor _).mapIso
        (F.leftDerivedFunctorIsoMapDerivedCategory.app J))).hom.app K) =
      (F.mapDerivedCategoryTensorComparison.app J).app K := by
  exact (transport_tensor_hom F.leftDerivedFunctorIsoMapDerivedCategory
    (fun J ↦ (asIso F.leftDerivedTensorComparison).app J) J K).trans
      (F.mapDerivedCategoryTensorComparison_app_app J K).symm

private theorem derived_comparison_braiding
    (hF : ∀ J K, F.map (β_ J K).hom ≫ Functor.OplaxMonoidal.δ F K J =
      Functor.OplaxMonoidal.δ F J K ≫ (β_ (F.obj J) (F.obj K)).hom)
    (J K : _root_.DerivedCategory C) :
    letI := _root_.DerivedCategory.braidedCategory' C
    letI := _root_.DerivedCategory.braidedCategory' D
    F.mapDerivedCategory.map (β_ J K).hom ≫
        (F.mapDerivedCategoryTensorComparison.app K).app J =
      (F.mapDerivedCategoryTensorComparison.app J).app K ≫
        (β_ (F.mapDerivedCategory.obj J) (F.mapDerivedCategory.obj K)).hom := by
  let := _root_.DerivedCategory.braidedCategory' C
  let := _root_.DerivedCategory.braidedCategory' D
  have ht := transport_braiding F.leftDerivedFunctorIsoMapDerivedCategory
    (fun J K ↦ (F.leftDerivedTensorComparison.app J).app K)
    (fun J K ↦ F.leftDerivedFunctor_map_braiding_hom_δ hF J K) J K
  simpa only [Functor.mapDerivedCategoryTensorComparison_app_app, Category.assoc] using ht

private theorem derived_comparison_koszul
    (hF : ∀ J K, F.map (β_ J K).hom ≫ Functor.OplaxMonoidal.δ F K J =
      Functor.OplaxMonoidal.δ F J K ≫ (β_ (F.obj J) (F.obj K)).hom)
    (J K : _root_.DerivedCategory C) :
    F.mapDerivedCategory.map (derivedTensorKoszulSymmetry C J K).hom ≫
        (F.mapDerivedCategoryTensorComparison.app K).app J =
      (F.mapDerivedCategoryTensorComparison.app J).app K ≫
        (derivedTensorKoszulSymmetry D
          (F.mapDerivedCategory.obj J) (F.mapDerivedCategory.obj K)).hom := by
  have h := derived_comparison_braiding F hF J K
  simpa only [derivedTensorKoszulSymmetry, BraidedCategory.braiding,
    _root_.DerivedCategory.braidedCategory', DerivedMonoidal.braidedCategory'] using h

private theorem canonical_symmetry_hom (J K : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app J).app K =
      (derivedTensorKoszulSymmetry C J K).hom := by
  rfl

private theorem comparison_tensor_eq
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (J K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A J).hom.app K =
      (((ProEtale.comparisonUpperStar A X).mapDerivedCategoryTensorComparison).app J).app K := by
  start_mate_proof
  · exact derived_comparison_tensor (ProEtale.comparisonUpperStar A X) J K
  · finish_mate_proof

private theorem comparison_underived_braiding
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (J K : Sheaf X.smallEtaleTopology A) :
    (ProEtale.comparisonUpperStar A X).map (β_ J K).hom ≫
        Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar A X) K J =
      Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar A X) J K ≫
        (β_ ((ProEtale.comparisonUpperStar A X).obj J)
          ((ProEtale.comparisonUpperStar A X).obj K)).hom := by
  have hb (U V : Sheaf (Scheme.ProEt.topology X) A) :
      Functor.LaxMonoidal.μ (ProEtale.comparisonLowerStar A X) U V ≫
          (ProEtale.comparisonLowerStar A X).map (β_ U V).hom =
        (β_ ((ProEtale.comparisonLowerStar A X).obj U)
          ((ProEtale.comparisonLowerStar A X).obj V)).hom ≫
          Functor.LaxMonoidal.μ (ProEtale.comparisonLowerStar A X) V U := by
    let : (ProEtale.comparisonLowerStar A X).LaxBraided := by
      dsimp only [ProEtale.comparisonLowerStar]
      infer_instance
    exact Functor.LaxBraided.braided U V
  exact adjunction_delta_braiding (ProEtale.comparisonAdjunction A X) hb J K

private theorem comparison_braiding
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (J K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ProEtale.comparisonUpperStar A X).mapDerivedCategory.map
        (derivedTensorKoszulSymmetry
          (Sheaf X.smallEtaleTopology A) J K).hom ≫
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        A K).hom.app J =
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        A J).hom.app K ≫
      (derivedTensorKoszulSymmetry
        (Sheaf (Scheme.ProEt.topology X) A)
        ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj J)
        ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj K)).hom := by
  start_mate_proof
  · rw [comparison_tensor_eq, comparison_tensor_eq]
    exact derived_comparison_koszul (ProEtale.comparisonUpperStar A X)
      (comparison_underived_braiding A X) J K
  · finish_mate_proof

/-- The etale-to-pro-etale comparison tensorator commutes with the signed derived
symmetries.  This is the localization of the signed total-complex exchange square.
Source: Stacks Project, Cohomology on Sites, Tag 07A4
(blueprint: lem-pur-comparison-tensorator-signed-symmetry).
Proof: choose flat-term K-flat representatives P and Q using site tensor descent.
The comparison is exact and induced termwise, so its tensorator is represented by
Tag 07A4's ordinary total-tensor comparison. ComparisonPullbackExact identifies
inverse-image constant coefficients with the pro-etale coefficient sheaf; hence
this is the ringed-topos pullback to which cochainPullbackTensorCoherence applies.
On each bidegree (p,q) summand, that comparison commutes with the signed exchange
(-1)^(p*q). Both derived symmetries are the localizations of precisely this signed
exchange. Localize the chain equation and insert the representative comparison
isomorphisms from site tensor descent. Their naturality makes this independent of
representatives, and the uniqueness clause descends the equation to all unbounded
M and N. Zero objects and degree-zero complexes satisfy the same identities. -/
theorem comparisonTensorator_signedSymmetry
    (A : Type (u + 1)) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] (T : Scheme.{u})
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
      (((AlgebraicGeometry.Etale.derivedTensorSymmetry
        (ModuleCat.{u + 1} A) T).hom.app M).app N) ≫
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) N).hom.app M =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).hom.app N ≫
      (CategoryTheory.derivedTensorKoszulSymmetry
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj N)).hom := by
  have hs (K L : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app L =
        (derivedTensorKoszulSymmetry
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) K L).hom :=
    canonical_symmetry_hom (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) K L
  rw [hs]
  exact comparison_braiding (ModuleCat.{u + 1} A) T M N

end AlgebraicGeometry.ProEtale
