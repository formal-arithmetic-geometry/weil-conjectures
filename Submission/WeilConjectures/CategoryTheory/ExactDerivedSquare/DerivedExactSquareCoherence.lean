/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Submission.WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Submission.WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Naturality of normalized right-derived squares

Source: Stacks Project, Cohomology on Sites, Tag 0D6E
(blueprint: lem-pur-derived-square-normalization-naturality).

A normalization by right-derived units determines a square on the derived category.
It therefore preserves ordinary naturality, horizontal composition, and commuting cubes.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactDerivedSquare
section
variable {A B Ap Bp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} Ap] [HasDerivedCategory.{w} Bp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  (F : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  [F.Additive] [G.Additive] [x.Additive] [y.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap] in
private theorem squareFactors
    (Fp : Bp ⥤ Ap) (F : B ⥤ A) (r : Ap ⥤ A) (s : Bp ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r ≅ s ⋙ F) (K : CochainComplex Bp ℤ) :
    (Functor.mapDerivedCategorySquareIso hF).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex hF (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fp r).inv.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem derived_unit_ext_general
    {E : Type (u + 1)} [Category.{u} E] [Abelian E] [HasDerivedCategory.{w} E]
    (Y : DerivedCategory.{w} B ⥤ DerivedCategory.{w} E)
    {T : DerivedCategory.{w} A ⥤ DerivedCategory.{w} E}
    (a b : F.rightDerivedFunctor ⋙ Y ⟶ T)
    (h : ∀ M : CochainComplex A ℤ,
      Y.map (F.rightDerivedFunctorUnitQ M) ≫ a.app (DerivedCategory.Q.obj M) =
        Y.map (F.rightDerivedFunctorUnitQ M) ≫ b.app (DerivedCategory.Q.obj M)) : a = b := by
  apply NatTrans.ext
  funext N
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := hI
  have : IsIso (F.rightDerivedFunctorUnitQ I) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hi : a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I) :=
    (cancel_epi (Y.map (F.rightDerivedFunctorUnitQ I))).mp (h I)
  apply (cancel_mono (T.map e.hom)).mp
  rw [← a.naturality e.hom, ← b.naturality e.hom, hi]

/-- A square normalized by the canonical right-derived units and localization factors.
Source: Stacks Tag 0D6E
(blueprint: lem-pur-derived-square-normalization-naturality). -/
def unitNormalized
    (X : DerivedCategory.{w} A ⥤ DerivedCategory.{w} Ap)
    (Y : DerivedCategory.{w} B ⥤ DerivedCategory.{w} Bp)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F ⋙ y ⟶ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ Y ⟶ X ⋙ G.rightDerivedFunctor) : Prop :=
  ∀ I : CochainComplex A ℤ,
    Y.map (F.rightDerivedFunctorUnitQ I) ≫ b.app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map (xf.hom.app I) =
      yf.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) ≫
        G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I)
omit [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y] in
/-- A square normalized by right-derived units respects a morphism of ordinary squares.
Source: Stacks Project, Cohomology on Sites, Tag 0D6E, uniqueness of right derivation.
(blueprint: lem-pur-derived-square-normalization-naturality).
Proof: evaluate on a K-injective representative, cancel the invertible source unit,
and use the two normalization equations. The ordinary square's naturality and the
naturality of the target derived unit then identify the two composites. Essential
surjectivity of K-injective representatives gives the equation on every object. -/
theorem normalized_naturality
    (x' : A ⥤ Ap) (y' : B ⥤ Bp) [x'.Additive] [y'.Additive]
    (X X' : DerivedCategory.{w} A ⥤ DerivedCategory.{w} Ap)
    (Y Y' : DerivedCategory.{w} B ⥤ DerivedCategory.{w} Bp)
    (xf : DerivedCategory.Q ⋙ X ≅ x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (xf' : DerivedCategory.Q ⋙ X' ≅ x'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf : DerivedCategory.Q ⋙ Y ≅ y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (yf' : DerivedCategory.Q ⋙ Y' ≅ y'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F ⋙ y ⟶ x ⋙ G) (c' : F ⋙ y' ⟶ x' ⋙ G)
    (b : F.rightDerivedFunctor ⋙ Y ⟶ X ⋙ G.rightDerivedFunctor)
    (b' : F.rightDerivedFunctor ⋙ Y' ⟶ X' ⋙ G.rightDerivedFunctor)
    (hn : unitNormalized F G x y X Y xf yf c b)
    (hn' : unitNormalized F G x' y' X' Y' xf' yf' c' b')
    (a : x ⟶ x') (d : y ⟶ y') (ad : X ⟶ X') (dd : Y ⟶ Y')
    (ha : ∀ I : CochainComplex A ℤ,
      ad.app (DerivedCategory.Q.obj I) ≫ xf'.hom.app I =
        xf.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I))
    (hd : ∀ I : CochainComplex B ℤ,
      dd.app (DerivedCategory.Q.obj I) ≫ yf'.hom.app I =
        yf.hom.app I ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex d (.up ℤ)).app I))
    (hc : ∀ M : A, d.app (F.obj M) ≫ c'.app M = c.app M ≫ G.map (a.app M)) :
    Functor.whiskerLeft F.rightDerivedFunctor dd ≫ b' =
      b ≫ Functor.whiskerRight ad G.rightDerivedFunctor := by
  apply derived_unit_ext_general F Y
  intro I
  apply (cancel_mono (G.rightDerivedFunctor.map (xf'.hom.app I))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [reassoc_of% dd.naturality (F.rightDerivedFunctorUnitQ I)]
  rw [hn' I]
  rw [reassoc_of% hd ((F.mapHomologicalComplex (.up ℤ)).obj I)]
  rw [← G.rightDerivedFunctor.map_comp, ha, Functor.map_comp]
  rw [reassoc_of% hn I]
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hcI :
      (NatTrans.mapHomologicalComplex d (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex c' (.up ℤ)).app I =
      (NatTrans.mapHomologicalComplex c (.up ℤ)).app I ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex a (.up ℤ)).app I) := by
    ext n
    exact hc (I.X n)
  rw [hcI, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rw [G.rightDerivedFunctorUnitQ_naturality]

private theorem normalized_comp
    {App Bpp : Type (u + 1)} [Category.{u} App] [Category.{u} Bpp]
    [Abelian App] [Abelian Bpp] [HasDerivedCategory.{w} App] [HasDerivedCategory.{w} Bpp]
    [Abelian.HasKInjectiveResolutions App]
    (H : App ⥤ Bpp) (x' : Ap ⥤ App) (y' : Bp ⥤ Bpp)
    [H.Additive] [x'.Additive] [y'.Additive]
    [PreservesFiniteLimits x'] [PreservesFiniteColimits x']
    [PreservesFiniteLimits y'] [PreservesFiniteColimits y']
    (c : F ⋙ y ≅ x ⋙ G) (c' : G ⋙ y' ≅ x' ⋙ H)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (b' : G.rightDerivedFunctor ⋙ y'.mapDerivedCategory ≅
      x'.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hb : unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom b.hom)
    (hb' : unitNormalized G H x' y' x'.mapDerivedCategory y'.mapDerivedCategory
      x'.mapDerivedCategoryFactors y'.mapDerivedCategoryFactors c'.hom b'.hom) :
    unitNormalized F H (x ⋙ x') (y ⋙ y')
      (x.mapDerivedCategory ⋙ x'.mapDerivedCategory)
      (y.mapDerivedCategory ⋙ y'.mapDerivedCategory)
      (Functor.isoWhiskerRight x.mapDerivedCategoryFactors x'.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (x.mapHomologicalComplex (.up ℤ)) x'.mapDerivedCategoryFactors)
      (Functor.isoWhiskerRight y.mapDerivedCategoryFactors y'.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (y.mapHomologicalComplex (.up ℤ)) y'.mapDerivedCategoryFactors)
      (Functor.whiskerRight c.hom y' ≫ Functor.whiskerLeft x c'.hom)
      (Functor.whiskerRight b.hom y'.mapDerivedCategory ≫
        Functor.whiskerLeft x.mapDerivedCategory b'.hom) := by
  intro I
  simp only [Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Category.assoc, Functor.map_comp]
  erw [← reassoc_of% b'.hom.naturality (x.mapDerivedCategoryFactors.hom.app I)]
  simp only [Functor.comp_obj]
  erw [← y'.mapDerivedCategory.map_comp_assoc, ← y'.mapDerivedCategory.map_comp_assoc]
  erw [Category.assoc, hb I]
  simp only [Functor.map_comp, Category.assoc]
  erw [hb' ((x.mapHomologicalComplex (.up ℤ)).obj I)]
  erw [reassoc_of% (y'.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I))]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  rfl

private theorem normalized_cube
    {App Bpp A2 B2 : Type (u + 1)}
    [Category.{u} App] [Category.{u} Bpp] [Category.{u} A2] [Category.{u} B2]
    [Abelian App] [Abelian Bpp] [Abelian A2] [Abelian B2]
    [HasDerivedCategory.{w} App] [HasDerivedCategory.{w} Bpp]
    [HasDerivedCategory.{w} A2] [HasDerivedCategory.{w} B2]
    [Abelian.HasKInjectiveResolutions App] [Abelian.HasKInjectiveResolutions A2]
    (H : App ⥤ Bpp) (K : A2 ⥤ B2)
    (x' : Ap ⥤ App) (y' : Bp ⥤ Bpp)
    (z : A ⥤ A2) (t : B ⥤ B2) (z' : A2 ⥤ App) (t' : B2 ⥤ Bpp)
    [H.Additive] [K.Additive] [x'.Additive] [y'.Additive]
    [z.Additive] [t.Additive] [z'.Additive] [t'.Additive]
    [PreservesFiniteLimits x'] [PreservesFiniteColimits x']
    [PreservesFiniteLimits y'] [PreservesFiniteColimits y']
    [PreservesFiniteLimits z] [PreservesFiniteColimits z]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    [PreservesFiniteLimits z'] [PreservesFiniteColimits z']
    [PreservesFiniteLimits t'] [PreservesFiniteColimits t']
    (c : F ⋙ y ≅ x ⋙ G) (c' : G ⋙ y' ≅ x' ⋙ H)
    (cc : F ⋙ t ≅ z ⋙ K) (cc' : K ⋙ t' ≅ z' ⋙ H)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (b' : G.rightDerivedFunctor ⋙ y'.mapDerivedCategory ≅
      x'.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (bb : F.rightDerivedFunctor ⋙ t.mapDerivedCategory ≅
      z.mapDerivedCategory ⋙ K.rightDerivedFunctor)
    (bb' : K.rightDerivedFunctor ⋙ t'.mapDerivedCategory ≅
      z'.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hb : unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom b.hom)
    (hb' : unitNormalized G H x' y' x'.mapDerivedCategory y'.mapDerivedCategory
      x'.mapDerivedCategoryFactors y'.mapDerivedCategoryFactors c'.hom b'.hom)
    (hbb : unitNormalized F K z t z.mapDerivedCategory t.mapDerivedCategory
      z.mapDerivedCategoryFactors t.mapDerivedCategoryFactors cc.hom bb.hom)
    (hbb' : unitNormalized K H z' t' z'.mapDerivedCategory t'.mapDerivedCategory
      z'.mapDerivedCategoryFactors t'.mapDerivedCategoryFactors cc'.hom bb'.hom)
    (a : x ⋙ x' ≅ z ⋙ z') (d : y ⋙ y' ≅ t ⋙ t')
    (hc : ∀ M : A,
      d.hom.app (F.obj M) ≫ t'.map (cc.hom.app M) ≫ cc'.hom.app (z.obj M) =
        y'.map (c.hom.app M) ≫ c'.hom.app (x.obj M) ≫ H.map (a.hom.app M))
    (N : DerivedCategory.{w} A) :
    y'.mapDerivedCategory.map (b.hom.app N) ≫ b'.hom.app (x.mapDerivedCategory.obj N) ≫
        H.rightDerivedFunctor.map ((Functor.mapDerivedCategorySquareIso a).hom.app N) =
      (Functor.mapDerivedCategorySquareIso d).hom.app (F.rightDerivedFunctor.obj N) ≫
        t'.mapDerivedCategory.map (bb.hom.app N) ≫ bb'.hom.app (z.mapDerivedCategory.obj N) := by
  let xf := Functor.isoWhiskerRight x.mapDerivedCategoryFactors x'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (x.mapHomologicalComplex (.up ℤ)) x'.mapDerivedCategoryFactors
  let yf := Functor.isoWhiskerRight y.mapDerivedCategoryFactors y'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (y.mapHomologicalComplex (.up ℤ)) y'.mapDerivedCategoryFactors
  let zf := Functor.isoWhiskerRight z.mapDerivedCategoryFactors z'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (z.mapHomologicalComplex (.up ℤ)) z'.mapDerivedCategoryFactors
  let tf := Functor.isoWhiskerRight t.mapDerivedCategoryFactors t'.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (t.mapHomologicalComplex (.up ℤ)) t'.mapDerivedCategoryFactors
  have h := normalized_naturality F H (x ⋙ x') (y ⋙ y') (z ⋙ z') (t ⋙ t')
    (x.mapDerivedCategory ⋙ x'.mapDerivedCategory)
    (z.mapDerivedCategory ⋙ z'.mapDerivedCategory)
    (y.mapDerivedCategory ⋙ y'.mapDerivedCategory)
    (t.mapDerivedCategory ⋙ t'.mapDerivedCategory) xf zf yf tf
    (Functor.whiskerRight c.hom y' ≫ Functor.whiskerLeft x c'.hom)
    (Functor.whiskerRight cc.hom t' ≫ Functor.whiskerLeft z cc'.hom)
    (Functor.whiskerRight b.hom y'.mapDerivedCategory ≫
      Functor.whiskerLeft x.mapDerivedCategory b'.hom)
    (Functor.whiskerRight bb.hom t'.mapDerivedCategory ≫
      Functor.whiskerLeft z.mapDerivedCategory bb'.hom)
    (normalized_comp F G x y H x' y' c c' b b' hb hb')
    (normalized_comp F K z t H z' t' cc cc' bb bb' hbb hbb')
    a.hom d.hom (Functor.mapDerivedCategorySquareIso a).hom
    (Functor.mapDerivedCategorySquareIso d).hom
    (fun I ↦ by simpa only [xf, zf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      NatIso.mapHomologicalComplex]
      using squareFactors x z' x' z a I)
    (fun I ↦ by simpa only [yf, tf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      NatIso.mapHomologicalComplex]
      using squareFactors y t' y' t d I)
    (fun M ↦ by simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hc M)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using (congrArg (fun q ↦ q.app N) h).symm
end
end CategoryTheory.ExactDerivedSquare
