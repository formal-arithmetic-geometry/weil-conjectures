/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import all WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import all WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.Algebra.Homology.Curve.KInjectiveResolutions
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import all WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Category.ULift
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import all WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.SmoothPurity.Ringed.RingedSiteKInjectiveResolutionsSupplement
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.SmoothPurity.Supporting.ChangeOfRingsKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange

/-! # Canonical comparisons for unbounded derived block functors

Source: Stacks Project, Tags 070I, 070Y, 08BJ and 09T5; Zheng Construction 4.1.
(blueprint: lem-pur-system-block-derived-comparisons).

This is the existing generic derived-comparison portion of SystemBlockRepetition,
extracted after coefficient-transport abstraction to keep each file within the
single-file compilation limit. All declarations and proofs retain their signatures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ u h w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

-- Elementary mate identities, proved locally to avoid depending on the geometric
-- normalization node. These proofs are the existing private mate calculations
-- from SectionDerivedPushpullNormalization (SHEAF group N9).
private theorem normalizedMate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv).natTrans = r.hom) (M : A) :
    b.unit.app (G.obj M) = G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (e.hom.app M) := by
  have h := unit_mateEquiv a b e.inv M
  change G.map (a.unit.app M) ≫ (mateEquiv a b e.inv).natTrans.app (L.obj M) = _ at h
  rw [hm] at h
  apply (cancel_mono (Rb.map (e.inv.app M))).mp
  simp only [Category.assoc, ← Rb.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

private theorem normalizedMate_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv).natTrans = r.hom) (N : B) :
    b.counit.app (H.obj N) = Lb.map (r.inv.app N) ≫ e.inv.app (R.obj N) ≫
      H.map (a.counit.app N) := by
  have h := mateEquiv_counit a b e.inv N
  change Lb.map ((mateEquiv a b e.inv).natTrans.app N) ≫ _ = _ at h
  rw [hm] at h
  apply (cancel_epi (Lb.map (r.hom.app N))).mp
  simp only [← Category.assoc, ← Lb.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h

section DerivedComparison

variable {X : Type u₁} {Y : Type u₂} {Xd : Type u₃} {Yd : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Xd] [Category.{v₄} Yd]
  [Abelian X] [Abelian Y] [Abelian Xd] [Abelian Yd]
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y]
  [HasDerivedCategory.{w₃} Xd] [HasDerivedCategory.{w₄} Yd]
  [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions Xd]
  (RX : X ⥤ Xd) (RY : Y ⥤ Yd) (G : X ⥤ Y) (GD : Xd ⥤ Yd)
  [RX.Additive] [RY.Additive] [G.Additive] [GD.Additive]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [RX.PreservesKInjectiveComplexes]

/-- The canonical comparison of total right derived functors, constructed from their
universal properties. In the system application the supplied square is identity on
sections, morphisms and transitions, so this is kappa_t of the node.
Source: Zheng 4.1 and paragraph before 4.10; Stacks 070Y
(blueprint: lem-pur-system-block-derived-comparisons). -/
def blockDerivedComparison (square : RX ⋙ GD ≅ G ⋙ RY) :
    RX.mapDerivedCategory ⋙ GD.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ RY.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIso RX GD).symm ≪≫
    Functor.rightDerivedFunctorNatIso square ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso G RY

/-- The identity comparison before localization, assembled with the canonical
termwise-composition identifications.
Source: Zheng 4.1, finite-block identity (blueprint: lem-pur-system-block-derived-comparisons). -/
def blockComplexComparison (square : RX ⋙ GD ≅ G ⋙ RY)
    (N : CochainComplex X ℤ) :
    (GD.mapHomologicalComplex (.up ℤ)).obj ((RX.mapHomologicalComplex (.up ℤ)).obj N) ≅
      (RY.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj N) :=
  ((Functor.mapHomologicalComplexCompIso (Iso.refl (RX ⋙ GD)) (.up ℤ)).app N).symm ≪≫
    (NatIso.mapHomologicalComplex square (.up ℤ)).app N ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).app N

attribute [local irreducible] blockComplexComparison

private theorem homotopyCompInv
    {A : Type*} {B : Type*} {D : Type*}
    [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    (F : A ⥤ B) (H : B ⥤ D) [F.Additive] [H.Additive]
    (K : HomotopyCategory A (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).inv.app K = 𝟙 _ := by
  have h := (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).hom_inv_id_app K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  exact h

private theorem comparisonFac (square : RX ⋙ GD ≅ G ⋙ RY)
    (K : HomotopyCategory X (.up ℤ)) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit RX GD).app K ≫
        (blockDerivedComparison RX RY G GD square).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory square.hom (.up ℤ)).app K) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit G RY).app K := by
  simp only [blockDerivedComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app RX GD K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc]
  rw [show (RX ⋙ GD).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso square).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory square.hom (.up ℤ)).app K) ≫
        (G ⋙ RY).rightDerivedFunctorUnit.app K by
    exact Functor.rightDerivedNatTrans_app _ _ _ _
      (HomotopyCategory.quasiIso X (.up ℤ)) _ K]
  simp only [Category.assoc]
  congr 1
  simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso]

attribute [local irreducible] blockDerivedComparison

private theorem factorsQuotient
    {A : Type*} {B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

private theorem factorsQuotientInv
    {A : Type*} {B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.inv.app P := by
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
  rw [← factorsQuotient F P, Iso.inv_hom_id_app, factorsQuotient, Iso.inv_hom_id_app]
  rfl

private theorem unitQuotient
    {A : Type*} {B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ) :
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.rightDerivedFunctorUnitQ P := by
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The defining unit equation, valid for EVERY complex, and uniqueness already from
K-injective representatives. It fixes all derived arrows and system transitions.
Source: Stacks 070I, 070Y; Zheng 4.1 finite-block generalization
(blueprint: lem-pur-system-block-derived-comparisons).
Proof: lem-sfb-grothendieck-k-injective supplies resolutions in the system application.
On K-injective I, RX I is K-injective by the endpoint adjunction, and both units are
invertible. The universal derived-functor comparison is their quotient, with the
ordinary square between them. By lem-sf-kinjective-derived-map-computation every
arrow between such representatives is a unique homotopy class; both routes apply
the identical repeated pushforward chain map to that class. This proves naturality,
resolution independence and uniqueness. For arbitrary N choose N→I. Naturality of
the units and the comparison reduces the equation to I after postcomposition by
an invertible derived resolution map; cancel it. No faithfulness of evaluation and
no preservation of K-injectives by scalar restriction is used. -/
theorem blockDerivedComparison_normalization (square : RX ⋙ GD ≅ G ⋙ RY) :
    (∀ N : CochainComplex X ℤ,
      GD.rightDerivedFunctorUnitQ ((RX.mapHomologicalComplex (.up ℤ)).obj N) ≫
        GD.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.inv.app N) ≫
        (blockDerivedComparison RX RY G GD square).hom.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Q.map (blockComplexComparison RX RY G GD square N).hom ≫
        RY.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj N) ≫
        RY.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ N)) ∧
    (∀ κ : RX.mapDerivedCategory ⋙ GD.rightDerivedFunctor ≅
        G.rightDerivedFunctor ⋙ RY.mapDerivedCategory,
      (∀ (I : CochainComplex X ℤ) [I.IsKInjective],
        GD.rightDerivedFunctorUnitQ ((RX.mapHomologicalComplex (.up ℤ)).obj I) ≫
          GD.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.inv.app I) ≫
          κ.hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map (blockComplexComparison RX RY G GD square I).hom ≫
          RY.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
          RY.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ I)) →
      κ = blockDerivedComparison RX RY G GD square) := by
  have hn : ∀ N : CochainComplex X ℤ,
      GD.rightDerivedFunctorUnitQ ((RX.mapHomologicalComplex (.up ℤ)).obj N) ≫
        GD.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.inv.app N) ≫
        (blockDerivedComparison RX RY G GD square).hom.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Q.map (blockComplexComparison RX RY G GD square N).hom ≫
        RY.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj N) ≫
        RY.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ N) := by
    intro N
    have h := comparisonFac RX RY G GD square
      ((HomotopyCategory.quotient X (.up ℤ)).obj N)
    simp only [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app,
      Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] at h
    erw [homotopyCompInv, DerivedCategory.Qh.map_id, Category.id_comp,
      homotopyCompInv, DerivedCategory.Qh.map_id, Category.id_comp] at h
    change (GD.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient Xd (.up ℤ)).obj
          ((RX.mapHomologicalComplex (.up ℤ)).obj N)) ≫
        GD.rightDerivedFunctor.map (RX.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient X (.up ℤ)).obj N))) ≫
        (blockDerivedComparison RX RY G GD square).hom.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Qh.map _ ≫ RY.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient Y (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj N)) ≫
        RY.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient X (.up ℤ)).obj N)) at h
    rw [unitQuotient, factorsQuotientInv, factorsQuotientInv, unitQuotient] at h
    have ht : (NatTrans.mapHomotopyCategory square.hom (.up ℤ)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatIso.mapHomologicalComplex square (.up ℤ)).hom.app N) := rfl
    rw [ht] at h
    have hq := DerivedCategory.quotientCompQhIso_hom_naturality
      ((NatIso.mapHomologicalComplex square (.up ℤ)).hom.app N)
    change DerivedCategory.Qh.map _ ≫ 𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map _ at hq
    simp only [Category.id_comp, Category.comp_id] at hq
    rw [hq] at h
    have hc : (blockComplexComparison RX RY G GD square N).hom =
        (NatIso.mapHomologicalComplex square (.up ℤ)).hom.app N := by
      have hi := (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RX ⋙ GD)) (.up ℤ)).hom_inv_id_app N
      rw [Functor.mapHomologicalComplexCompIso_refl_hom_app, Category.id_comp] at hi
      simp only [blockComplexComparison, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Iso.app_inv,
        Functor.mapHomologicalComplexCompIso_refl_hom_app, hi]
      erw [Category.id_comp, Category.comp_id]
    rw [hc]
    simpa only [Category.assoc] using h
  refine ⟨hn, ?_⟩
  intro κ hκ
  apply Iso.ext
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := X))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨I, hI, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  change κ.hom.app (DerivedCategory.Q.obj I) =
    (blockDerivedComparison RX RY G GD square).hom.app (DerivedCategory.Q.obj I)
  have hu : IsIso (GD.rightDerivedFunctorUnitQ
      ((RX.mapHomologicalComplex (.up ℤ)).obj I)) := by
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  apply (cancel_epi (GD.rightDerivedFunctorUnitQ
    ((RX.mapHomologicalComplex (.up ℤ)).obj I) ≫
      GD.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.inv.app I))).mp
  simpa only [Category.assoc] using (hκ I).trans (hn I).symm

section InverseComparison
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
  [F.Additive] [G.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [R.PreservesKInjectiveComplexes]

private def derived_square (e : F ⋙ S ≅ R ⋙ G) :
    F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (blockDerivedComparison R S F G e.symm).symm

private theorem square_fac (e : F ⋙ S ≅ R ⋙ G)
    (K : HomotopyCategory A (.up ℤ)) :
    S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        (derived_square F G R S e).hom.app (DerivedCategory.Qh.obj K) =
      S.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (R.mapDerivedCategoryFactorsh.inv.app K) := by
  have hf := comparisonFac R S F G e.symm K
  simp only [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, homotopyCompInv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Iso.symm_hom, Category.assoc] at hf
  erw [Category.id_comp] at hf
  apply (cancel_mono ((blockDerivedComparison R S F G e.symm).hom.app
    (DerivedCategory.Qh.obj K))).mp
  simp only [derived_square, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [hf]
  simp only [← DerivedCategory.Qh.map_comp_assoc, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  erw [Category.comp_id]
end InverseComparison

section Canonical
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
  [F.Additive] [G.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

private theorem inverseEq [R.PreservesKInjectiveComplexes] (e : F ⋙ S ≅ R ⋙ G) :
    (blockDerivedComparison R S F G e.symm).inv =
      AlgebraicGeometry.Etale.derivedSquare e.hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let K := (HomotopyCategory.quotient A (.up ℤ)).obj I
  change (blockDerivedComparison R S F G e.symm).inv.app (DerivedCategory.Qh.obj K) =
    (AlgebraicGeometry.Etale.derivedSquare e.hom).app (DerivedCategory.Qh.obj K)
  apply (cancel_epi (S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K))).mp
  have hf := square_fac F G R S e K
  apply (cancel_epi (S.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
  simp only [derived_square, Iso.symm_hom] at hf ⊢
  erw [hf]
  simp only [Iso.inv_hom_id_app_assoc]
  exact (AlgebraicGeometry.Etale.derivedSquare_app_fac e.hom K).symm
end Canonical

/-- Compatibility with the actual geometric adjunctions, expressed as both equations.
The ordinary inverse square and direct square are the strict levelwise identities
in the application; the ordinary unit and counit equations exclude a twisted adjunction.
Source: Zheng 4.1 and geometric morphism paragraph before 4.10; Stacks 09T5
(blueprint: lem-pur-system-block-derived-comparisons).
Proof: apply lem-weil-pbc-exact-square-derived-counit to the inverse of the normalized
comparison; its normalization is blockDerivedComparison_normalization at K-injectives.
The right adjoints are derived from the specified ordinary adjunctions. Their
transposes on K-injectives are ordinary transposes followed by the derived units.
Repetition preserves those componentwise words. The transpose of the identity is
the derived unit, giving the first equation; the exact-square theorem gives the second.
Resolution comparison extends them to all objects. -/
theorem blockDerivedComparison_adjunction
    (square : RX ⋙ GD ≅ G ⋙ RY)
    (F : Y ⥤ X) (FD : Yd ⥤ Xd) [F.Additive] [FD.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits FD] [PreservesFiniteColimits FD]
    (adj : F ⊣ G) (adjd : FD ⊣ GD)
    (pullSquare : F ⋙ RX ≅ RY ⋙ FD)
    (unit : ∀ M : Y,
      RY.map (adj.unit.app M) ≫ square.inv.app (F.obj M) ≫
          GD.map (pullSquare.hom.app M) = adjd.unit.app (RY.obj M))
    (counit : ∀ N : X,
      FD.map (square.inv.app N) ≫ adjd.counit.app (RX.obj N) =
        pullSquare.inv.app (G.obj N) ≫ RX.map (adj.counit.app N)) :
    (∀ M : DerivedCategory Y,
      RY.mapDerivedCategory.map
          (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
        (blockDerivedComparison RX RY G GD square).inv.app (F.mapDerivedCategory.obj M) ≫
        GD.rightDerivedFunctor.map
          ((Functor.mapDerivedCategorySquareIso pullSquare).hom.app M) =
      adjd.mapDerivedCategoryRightDerivedAdjunction.unit.app (RY.mapDerivedCategory.obj M)) ∧
    (∀ N : DerivedCategory X,
      FD.mapDerivedCategory.map ((blockDerivedComparison RX RY G GD square).inv.app N) ≫
        adjd.mapDerivedCategoryRightDerivedAdjunction.counit.app (RX.mapDerivedCategory.obj N) =
      (Functor.mapDerivedCategorySquareIso pullSquare).inv.app (G.rightDerivedFunctor.obj N) ≫
        RX.mapDerivedCategory.map
          (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app N)) := by
  have _ := counit
  have hm : (mateEquiv adj adjd pullSquare.inv).natTrans = square.inv := by
    apply AlgebraicGeometry.Etale.mate_eq_of_unit
    intro M
    apply (cancel_mono (GD.map (pullSquare.hom.app M))).mp
    simp only [Category.assoc, ← GD.map_comp, Iso.inv_hom_id_app]
    erw [GD.map_id, Category.comp_id]
    exact (unit M).symm
  let ds := Functor.mapDerivedCategorySquareIso pullSquare
  let dr := (blockDerivedComparison RX RY G GD square).symm
  have hdm : (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adjd.mapDerivedCategoryRightDerivedAdjunction ds.inv).natTrans = dr.hom := by
    have h := AlgebraicGeometry.Etale.derived_mate_exact_inv_eq_square adj adjd pullSquare
    change (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adjd.mapDerivedCategoryRightDerivedAdjunction ds.inv).natTrans =
        AlgebraicGeometry.Etale.derivedSquare
          (mateEquiv adj adjd pullSquare.inv).natTrans at h
    rw [hm] at h
    have hi := inverseEq G GD RX RY square.symm
    change dr.hom = AlgebraicGeometry.Etale.derivedSquare square.inv at hi
    exact h.trans hi.symm
  constructor
  · intro M
    exact (normalizedMate_unit adj.mapDerivedCategoryRightDerivedAdjunction
      adjd.mapDerivedCategoryRightDerivedAdjunction ds dr hdm M).symm
  · intro N
    have h := normalizedMate_counit adj.mapDerivedCategoryRightDerivedAdjunction
      adjd.mapDerivedCategoryRightDerivedAdjunction ds dr hdm N
    change FD.mapDerivedCategory.map (dr.hom.app N) ≫ _ = _
    rw [h]
    simp only [← FD.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl


end DerivedComparison
section CoefficientComparison

variable {X : Type u₁} {Y : Type u₂} {Xp : Type u₃} {Yp : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Xp] [Category.{v₄} Yp]
  [Abelian X] [Abelian Y] [Abelian Xp] [Abelian Yp]
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y]
  [HasDerivedCategory.{w₃} Xp] [HasDerivedCategory.{w₄} Yp]
  [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions Xp]
  (UX : Xp ⥤ X) (UY : Yp ⥤ Y) (G : X ⥤ Y) (Gp : Xp ⥤ Yp)
  [UX.Additive] [UY.Additive] [G.Additive] [Gp.Additive]
  [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
  [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]

/-- The canonical coefficient comparison beta, constructed by the total-derived
universal property. UX and UY are exact restrictions of scalars in the application.
There is deliberately no K-injective-preservation or invertibility assumption on UX.
Source: Stacks 070Y; Zheng 4.1 coefficient compatibility
(blueprint: lem-pur-system-block-derived-comparisons). -/
def blockCoefficientComparison (square : Gp ⋙ UY ≅ UX ⋙ G) :
    Gp.rightDerivedFunctor ⋙ UY.mapDerivedCategory ⟶
      UX.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso Gp UY).inv ≫
    Functor.rightDerivedPullback UX square.hom

attribute [local irreducible] blockCoefficientComparison

end CoefficientComparison
section Canonical
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
  [F.Additive] [G.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

private theorem coefficientFac (e : F ⋙ S ≅ R ⋙ G)
    (K : HomotopyCategory A (.up ℤ)) :
    S.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      (WeilConjectures.SemilinearSections.blockCoefficientComparison R S G F e).app
        (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
      G.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      G.rightDerivedFunctor.map (R.mapDerivedCategoryFactorsh.inv.app K) := by
  have hf := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac F S K
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at hf
  simp only [WeilConjectures.SemilinearSections.blockCoefficientComparison,
    NatTrans.comp_app]
  rw [← Category.assoc, ← hf]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact Functor.rightDerivedPullback_fac_app R e.hom P

private theorem coefficientEq (e : F ⋙ S ≅ R ⋙ G) :
    WeilConjectures.SemilinearSections.blockCoefficientComparison R S G F e =
      AlgebraicGeometry.Etale.derivedSquare e.hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let K := (HomotopyCategory.quotient A (.up ℤ)).obj I
  apply (cancel_epi (S.mapDerivedCategoryFactorsh.inv.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K))).mp
  simp only [Category.assoc]
  exact (coefficientFac F G R S e K).trans
    (AlgebraicGeometry.Etale.derivedSquare_app_fac e.hom K).symm

end Canonical

section CoefficientNaturality

variable {X Y Xd Yd Xp Yp Xdp Ydp : Type u}
  [Category.{h} X] [Category.{h} Y] [Category.{h} Xd] [Category.{h} Yd]
  [Category.{h} Xp] [Category.{h} Yp] [Category.{h} Xdp] [Category.{h} Ydp]
  [Abelian X] [Abelian Y] [Abelian Xd] [Abelian Yd]
  [Abelian Xp] [Abelian Yp] [Abelian Xdp] [Abelian Ydp]
  [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
  [HasDerivedCategory.{w} Xd] [HasDerivedCategory.{w} Yd]
  [HasDerivedCategory.{w} Xp] [HasDerivedCategory.{w} Yp]
  [HasDerivedCategory.{w} Xdp] [HasDerivedCategory.{w} Ydp]
  [Abelian.HasKInjectiveResolutions X] [Abelian.HasKInjectiveResolutions Xd]
  [Abelian.HasKInjectiveResolutions Xp] [Abelian.HasKInjectiveResolutions Xdp]
  (RX : X ⥤ Xd) (RY : Y ⥤ Yd) (RXp : Xp ⥤ Xdp) (RYp : Yp ⥤ Ydp)
  (UX : Xp ⥤ X) (UY : Yp ⥤ Y) (UXd : Xdp ⥤ Xd) (UYd : Ydp ⥤ Yd)
  (G : X ⥤ Y) (GD : Xd ⥤ Yd) (Gp : Xp ⥤ Yp) (GDp : Xdp ⥤ Ydp)
  [RX.Additive] [RY.Additive] [RXp.Additive] [RYp.Additive]
  [UX.Additive] [UY.Additive] [UXd.Additive] [UYd.Additive]
  [G.Additive] [GD.Additive] [Gp.Additive] [GDp.Additive]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [PreservesFiniteLimits RXp] [PreservesFiniteColimits RXp]
  [PreservesFiniteLimits RYp] [PreservesFiniteColimits RYp]
  [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
  [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
  [PreservesFiniteLimits UXd] [PreservesFiniteColimits UXd]
  [PreservesFiniteLimits UYd] [PreservesFiniteColimits UYd]
  [RX.PreservesKInjectiveComplexes] [RXp.PreservesKInjectiveComplexes]

/-- The coefficient equation for the canonical universal comparisons beta_b and beta_d.
For strict reindexing identities ex and ey are the identity section comparisons, and
this is kappa_B U_b after beta_d = R beta_b after U_d kappa_B'.
Source: Zheng 4.1 finite-block generalization; Stacks 070Y
(blueprint: lem-pur-system-block-derived-comparisons).
Proof: choose a K-injective B'-system representative I. RXp I is K-injective by
the exact endpoint adjunction. Precompose the equation with UYd of the invertible
right-derived unit at RXp I. The defining universal factorizations of beta_d and
beta_b, followed by blockDerivedComparison_normalization (valid even on UX I),
reduce both routes to RY of the right-derived unit at UX I. The ordinary cube
identifies the intervening maps. Cancel the invertible precomposition. Every object
has such a representative, and naturality extends equality to all derived arrows.
Neither UX I being K-injective nor either beta being invertible is assumed. -/
theorem blockCoefficientComparison_naturality
    (s : RX ⋙ GD ≅ G ⋙ RY) (sp : RXp ⋙ GDp ≅ Gp ⋙ RYp)
    (b : Gp ⋙ UY ≅ UX ⋙ G) (d : GDp ⋙ UYd ≅ UXd ⋙ GD)
    (ex : RXp ⋙ UXd ≅ UX ⋙ RX) (ey : RYp ⋙ UYd ≅ UY ⋙ RY)
    (cube : ∀ N : Xp,
      d.hom.app (RXp.obj N) ≫ GD.map (ex.hom.app N) ≫ s.hom.app (UX.obj N) =
      UYd.map (sp.hom.app N) ≫ ey.hom.app (Gp.obj N) ≫ RY.map (b.hom.app N)) :
    ∀ N : DerivedCategory Xp,
      (blockCoefficientComparison UXd UYd GD GDp d).app (RXp.mapDerivedCategory.obj N) ≫
        GD.rightDerivedFunctor.map ((Functor.mapDerivedCategorySquareIso ex).hom.app N) ≫
        (blockDerivedComparison RX RY G GD s).hom.app (UX.mapDerivedCategory.obj N) =
      UYd.mapDerivedCategory.map ((blockDerivedComparison RXp RYp Gp GDp sp).hom.app N) ≫
        (Functor.mapDerivedCategorySquareIso ey).hom.app (Gp.rightDerivedFunctor.obj N) ≫
        RY.mapDerivedCategory.map ((blockCoefficientComparison UX UY G Gp b).app N) := by
  intro N
  have hc : ∀ M : Xp,
      UYd.map (sp.inv.app M) ≫ d.hom.app (RXp.obj M) ≫ GD.map (ex.hom.app M) =
        ey.hom.app (Gp.obj M) ≫ RY.map (b.hom.app M) ≫ s.inv.app (UX.obj M) := by
    intro M
    apply (cancel_epi (UYd.map (sp.hom.app M))).mp
    apply (cancel_mono (s.hom.app (UX.obj M))).mp
    simp only [Category.assoc, ← UYd.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact cube M
  have ht := AlgebraicGeometry.Etale.derivedSquare_cube
    Gp GDp G GD RXp RYp RX RY UX UY UXd UYd
    sp.inv s.inv b.hom d.hom ey.symm ex.symm hc N
  have hp := (inverseEq Gp GDp RXp RYp sp.symm).symm
  change AlgebraicGeometry.Etale.derivedSquare sp.inv =
    (blockDerivedComparison RXp RYp Gp GDp sp).inv at hp
  have hs := (inverseEq G GD RX RY s.symm).symm
  change AlgebraicGeometry.Etale.derivedSquare s.inv =
    (blockDerivedComparison RX RY G GD s).inv at hs
  rw [hp, hs, ← coefficientEq Gp G UX UY b, ← coefficientEq GDp GD UXd UYd d] at ht
  have hex : ((Functor.mapDerivedCategoryCompIso UX RX).symm ≪≫
      Functor.mapDerivedCategoryNatIso ex.symm ≪≫
      Functor.mapDerivedCategoryCompIso RXp UXd).inv =
        (Functor.mapDerivedCategorySquareIso ex).hom := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
    have hi := Functor.mapDerivedCategoryNatIso_symm ex.symm
    change (Functor.mapDerivedCategoryNatIso ex).hom =
      (Functor.mapDerivedCategoryNatIso ex.symm).inv at hi
    rw [hi]
  have hey : ((Functor.mapDerivedCategoryCompIso UY RY).symm ≪≫
      Functor.mapDerivedCategoryNatIso ey.symm ≪≫
      Functor.mapDerivedCategoryCompIso RYp UYd).inv =
        (Functor.mapDerivedCategorySquareIso ey).hom := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
    have hi := Functor.mapDerivedCategoryNatIso_symm ey.symm
    change (Functor.mapDerivedCategoryNatIso ey).hom =
      (Functor.mapDerivedCategoryNatIso ey.symm).inv at hi
    rw [hi]
  rw [hex, hey] at ht
  apply (cancel_epi (UYd.mapDerivedCategory.map
    ((blockDerivedComparison RXp RYp Gp GDp sp).inv.app N))).mp
  apply (cancel_mono ((blockDerivedComparison RX RY G GD s).inv.app
    (UX.mapDerivedCategory.obj N))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simp only [← UYd.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ht


end CoefficientNaturality

section ExactComposition
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private noncomputable def exact_comp (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

private lemma exact_comp_hom_fac (e : F ⋙ G ≅ H)
    (K : HomotopyCategory A (.up ℤ)) :
    (exact_comp F G H e).hom.app (DerivedCategory.Qh.obj K) ≫
      H.mapDerivedCategoryFactorsh.hom.app K =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [exact_comp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fach]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).hom.app
    (DerivedCategory.Q.obj P))).1
  erw [Iso.hom_inv_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]
  rfl

private lemma exact_comp_fac (e : F ⋙ G ≅ H) (K : HomotopyCategory A (.up ℤ)) :
    G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app K) ≫
      (exact_comp F G H e).hom.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
      H.mapDerivedCategoryFactorsh.inv.app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  apply (cancel_mono (H.mapDerivedCategoryFactorsh.hom.app _)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [exact_comp_hom_fac]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Category.comp_id]
end ExactComposition

section HorizontalComposition
variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
  (R : A ⥤ B) (S : B ⥤ C) (T : A ⥤ C)
  (R' : A' ⥤ B') (S' : B' ⥤ C') (T' : A' ⥤ C')
  [F.Additive] [G.Additive] [H.Additive]
  [R.Additive] [S.Additive] [T.Additive] [R'.Additive] [S'.Additive] [T'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
  [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
  [R.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
  [T.PreservesKInjectiveComplexes]
  (e : F ⋙ R' ≅ R ⋙ G) (d : G ⋙ S' ≅ S ⋙ H) (c : F ⋙ T' ≅ T ⋙ H)
  (r : R ⋙ S ≅ T) (s : R' ⋙ S' ≅ T')

-- Localization reduces coherence of these canonical squares to the ordinary identity.
private lemma square_horizontal
    (he : ∀ K : A, S'.map (e.hom.app K) ≫ d.hom.app (R.obj K) ≫
      H.map (r.hom.app K) = s.hom.app (F.obj K) ≫ c.hom.app K) :
    Functor.whiskerRight (derived_square F G R R' e).hom S'.mapDerivedCategory ≫
      Functor.whiskerLeft R.mapDerivedCategory (derived_square G H S S' d).hom ≫
      Functor.whiskerRight (exact_comp R S T r).hom H.rightDerivedFunctor =
    Functor.whiskerLeft F.rightDerivedFunctor (exact_comp R' S' T' s).hom ≫
      (derived_square F H T T' c).hom := by
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := A))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let qK := (HomotopyCategory.quotient A (.up ℤ)).obj K
  apply (cancel_epi (S'.mapDerivedCategory.map (R'.mapDerivedCategory.map
    (F.rightDerivedFunctorUnit.app qK)))).1
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change S'.mapDerivedCategory.map (R'.mapDerivedCategory.map
      (F.rightDerivedFunctorUnit.app qK)) ≫
      S'.mapDerivedCategory.map ((derived_square F G R R' e).hom.app
        (DerivedCategory.Qh.obj qK)) ≫
      (derived_square G H S S' d).hom.app (R.mapDerivedCategory.obj
        (DerivedCategory.Qh.obj qK)) ≫
      H.rightDerivedFunctor.map ((exact_comp R S T r).hom.app
        (DerivedCategory.Qh.obj qK)) =
    S'.mapDerivedCategory.map (R'.mapDerivedCategory.map
      (F.rightDerivedFunctorUnit.app qK)) ≫
      (exact_comp R' S' T' s).hom.app (F.rightDerivedFunctor.obj
        (DerivedCategory.Qh.obj qK)) ≫
      (derived_square F H T T' c).hom.app (DerivedCategory.Qh.obj qK)
  have hf := square_fac F G R R' e qK
  have hg := square_fac G H S S' d ((R.mapHomotopyCategory (.up ℤ)).obj qK)
  have hn := (derived_square G H S S' d).hom.naturality
    (R.mapDerivedCategoryFactorsh.inv.app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← S'.mapDerivedCategory.map_comp_assoc, hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hg]
  have hfac := S'.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hfac
  erw [reassoc_of% hfac]
  erw [← H.rightDerivedFunctor.map_comp]
  erw [← H.rightDerivedFunctor.map_comp]
  erw [exact_comp_fac R S T r qK]
  have hη := H.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hη
  rw [Functor.map_comp]
  erw [← reassoc_of% hη]
  have hnat := (exact_comp R' S' T' s).hom.naturality
    (F.rightDerivedFunctorUnit.app qK)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [reassoc_of% hnat, square_fac]
  rw [reassoc_of% (exact_comp_hom_fac R' S' T' s
    ((F.mapHomotopyCategory (.up ℤ)).obj qK))]
  have hh : (S'.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app qK) ≫
      (NatTrans.mapHomotopyCategory d.hom (.up ℤ)).app
        ((R.mapHomotopyCategory (.up ℤ)).obj qK) ≫
      (H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app qK) =
    (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj qK) ≫
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app qK := by
    have hc : (S'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) ≫
        (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K := by
      ext n
      exact he (K.X n)
    have hq := (HomotopyCategory.quotient C' (.up ℤ)).congr_map hc
    change (HomotopyCategory.quotient C' (.up ℤ)).map
        ((S'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)) ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
            ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map
          ((H.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex r.hom (.up ℤ)).app K)) =
      (HomotopyCategory.quotient C' (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app
            ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        (HomotopyCategory.quotient C' (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app K)
    simpa only [Functor.map_comp] using hq
  rw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
  simp only [Category.assoc] at hh ⊢
  erw [hh]
  simp only [Functor.map_comp, Category.assoc]
  rfl
end HorizontalComposition


section Composition

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type u}
  [Category.{h} X₀] [Category.{h} X₁] [Category.{h} X₂]
  [Category.{h} Y₀] [Category.{h} Y₁] [Category.{h} Y₂]
  [Abelian X₀] [Abelian X₁] [Abelian X₂]
  [Abelian Y₀] [Abelian Y₁] [Abelian Y₂]
  [HasDerivedCategory.{w} X₀] [HasDerivedCategory.{w} X₁] [HasDerivedCategory.{w} X₂]
  [HasDerivedCategory.{w} Y₀] [HasDerivedCategory.{w} Y₁] [HasDerivedCategory.{w} Y₂]
  [Abelian.HasKInjectiveResolutions X₀] [Abelian.HasKInjectiveResolutions X₁]
  [Abelian.HasKInjectiveResolutions X₂]
  (RX₀₁ : X₀ ⥤ X₁) (RX₁₂ : X₁ ⥤ X₂) (RX₀₂ : X₀ ⥤ X₂)
  (RY₀₁ : Y₀ ⥤ Y₁) (RY₁₂ : Y₁ ⥤ Y₂) (RY₀₂ : Y₀ ⥤ Y₂)
  (G₀ : X₀ ⥤ Y₀) (G₁ : X₁ ⥤ Y₁) (G₂ : X₂ ⥤ Y₂)
  [RX₀₁.Additive] [RX₁₂.Additive] [RX₀₂.Additive]
  [RY₀₁.Additive] [RY₁₂.Additive] [RY₀₂.Additive]
  [G₀.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits RX₀₁] [PreservesFiniteColimits RX₀₁]
  [PreservesFiniteLimits RX₁₂] [PreservesFiniteColimits RX₁₂]
  [PreservesFiniteLimits RX₀₂] [PreservesFiniteColimits RX₀₂]
  [PreservesFiniteLimits RY₀₁] [PreservesFiniteColimits RY₀₁]
  [PreservesFiniteLimits RY₁₂] [PreservesFiniteColimits RY₁₂]
  [PreservesFiniteLimits RY₀₂] [PreservesFiniteColimits RY₀₂]
  [RX₀₁.PreservesKInjectiveComplexes] [RX₁₂.PreservesKInjectiveComplexes]
  [RX₀₂.PreservesKInjectiveComplexes]

/-- Comparison for a composite reindexing is the composite of the comparisons.
Source: Zheng 4.1 finite-block generalization; Stacks 070Y
(blueprint: lem-pur-system-block-derived-comparisons).
Proof: on a K-injective representative all three repeated complexes are K-injective.
Substitute blockDerivedComparison_normalization twice. The intervening unit and its
inverse cancel, and the ordinary composition equation identifies the remaining
chain map with that for the composite. Uniqueness in the same normalization theorem
extends equality to the whole ordinary derived category, on objects and arrows. -/
theorem blockDerivedComparison_comp
    (s₀₁ : RX₀₁ ⋙ G₁ ≅ G₀ ⋙ RY₀₁) (s₁₂ : RX₁₂ ⋙ G₂ ≅ G₁ ⋙ RY₁₂)
    (s₀₂ : RX₀₂ ⋙ G₂ ≅ G₀ ⋙ RY₀₂)
    (ex : RX₀₁ ⋙ RX₁₂ ≅ RX₀₂) (ey : RY₀₁ ⋙ RY₁₂ ≅ RY₀₂)
    (coherent : ∀ N : X₀,
      G₂.map (ex.hom.app N) ≫ s₀₂.hom.app N =
      s₁₂.hom.app (RX₀₁.obj N) ≫ RY₁₂.map (s₀₁.hom.app N) ≫ ey.hom.app (G₀.obj N)) :
    ∀ N : DerivedCategory X₀,
      G₂.rightDerivedFunctor.map ((Functor.mapDerivedCategoryCompNatIso ex).hom.app N) ≫
        (blockDerivedComparison RX₀₂ RY₀₂ G₀ G₂ s₀₂).hom.app N =
      (blockDerivedComparison RX₁₂ RY₁₂ G₁ G₂ s₁₂).hom.app (RX₀₁.mapDerivedCategory.obj N) ≫
        RY₁₂.mapDerivedCategory.map ((blockDerivedComparison RX₀₁ RY₀₁ G₀ G₁ s₀₁).hom.app N) ≫
        (Functor.mapDerivedCategoryCompNatIso ey).hom.app (G₀.rightDerivedFunctor.obj N) := by
  intro N
  have hc : ∀ M : X₀,
      RY₁₂.map (s₀₁.inv.app M) ≫ s₁₂.inv.app (RX₀₁.obj M) ≫
        G₂.map (ex.hom.app M) = ey.hom.app (G₀.obj M) ≫ s₀₂.inv.app M := by
    intro M
    apply (cancel_mono (s₀₂.hom.app M)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [coherent]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    erw [Category.comp_id]
  have ht := congr_app
    (square_horizontal G₀ G₁ G₂ RX₀₁ RX₁₂ RX₀₂ RY₀₁ RY₁₂ RY₀₂
      s₀₁.symm s₁₂.symm s₀₂.symm ex ey hc) N
  change RY₁₂.mapDerivedCategory.map
      ((blockDerivedComparison RX₀₁ RY₀₁ G₀ G₁ s₀₁).inv.app N) ≫
      (blockDerivedComparison RX₁₂ RY₁₂ G₁ G₂ s₁₂).inv.app
        (RX₀₁.mapDerivedCategory.obj N) ≫
      G₂.rightDerivedFunctor.map ((Functor.mapDerivedCategoryCompNatIso ex).hom.app N) =
    (Functor.mapDerivedCategoryCompNatIso ey).hom.app (G₀.rightDerivedFunctor.obj N) ≫
      (blockDerivedComparison RX₀₂ RY₀₂ G₀ G₂ s₀₂).inv.app N at ht
  apply (cancel_epi (RY₁₂.mapDerivedCategory.map
      ((blockDerivedComparison RX₀₁ RY₀₁ G₀ G₁ s₀₁).inv.app N) ≫
    (blockDerivedComparison RX₁₂ RY₁₂ G₁ G₂ s₁₂).inv.app
      (RX₀₁.mapDerivedCategory.obj N))).mp
  apply (cancel_mono ((blockDerivedComparison RX₀₂ RY₀₂ G₀ G₂ s₀₂).inv.app N)).mp
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc, ← RY₁₂.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]
  exact ht


end Composition

private theorem exactIdentityFac
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 A) (K : HomotopyCategory A (.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app K ≫
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Functor.mapDerivedCategoryNatIso_fach]
  simp

section Identity

variable {X Y : Type u} [Category.{h} X] [Category.{h} Y] [Abelian X] [Abelian Y]
  [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
  [Abelian.HasKInjectiveResolutions X]
  (RX : X ⥤ X) (RY : Y ⥤ Y) (G : X ⥤ Y)
  [RX.Additive] [RY.Additive] [G.Additive]
  [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
  [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
  [RX.PreservesKInjectiveComplexes]

/-- The identity block comparison is identity under the canonical identity reindexings.
Source: Zheng 4.1 identity case; Stacks 070Y (blueprint: lem-pur-system-block-derived-comparisons).
Proof: substitute the identity ordinary square into the normalization equation.
The two derived units coincide, and their inverse/hom pair cancels on K-injectives.
Uniqueness extends the identity to all objects and maps. -/
theorem blockDerivedComparison_id (square : RX ⋙ G ≅ G ⋙ RY)
    (ex : RX ≅ 𝟭 X) (ey : RY ≅ 𝟭 Y)
    (coherent : ∀ N : X, square.hom.app N ≫ ey.hom.app (G.obj N) = G.map (ex.hom.app N)) :
    ∀ N : DerivedCategory X,
      (blockDerivedComparison RX RY G G square).hom.app N ≫
        (Functor.mapDerivedCategoryNatIso ey ≪≫ Functor.mapDerivedCategoryIdIso Y).hom.app
          (G.rightDerivedFunctor.obj N) =
      G.rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso ex ≪≫ Functor.mapDerivedCategoryIdIso X).hom.app N) := by
  let dx := Functor.mapDerivedCategoryNatIso ex ≪≫ Functor.mapDerivedCategoryIdIso X
  let dy := Functor.mapDerivedCategoryNatIso ey ≪≫ Functor.mapDerivedCategoryIdIso Y
  let α : RX.mapDerivedCategory ⋙ G.rightDerivedFunctor ⟶ G.rightDerivedFunctor :=
    (blockDerivedComparison RX RY G G square).hom ≫
      Functor.whiskerLeft G.rightDerivedFunctor dy.hom
  let β : RX.mapDerivedCategory ⋙ G.rightDerivedFunctor ⟶ G.rightDerivedFunctor :=
    Functor.whiskerRight dx.hom G.rightDerivedFunctor
  suffices α = β from fun N ↦ congr_app this N
  apply Localization.natTrans_ext (HomotopyCategory.KInjectives.Qh (C := X))
    (MorphismProperty.isomorphisms _)
  intro I
  obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
  let K := (HomotopyCategory.quotient X (.up ℤ)).obj I
  have hi : IsIso (G.rightDerivedFunctorUnit.app
      ((RX.mapHomotopyCategory (.up ℤ)).obj K)) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient X (.up ℤ)).obj
        ((RX.mapHomologicalComplex (.up ℤ)).obj I))))
  apply (cancel_epi (G.rightDerivedFunctorUnit.app
      ((RX.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (RX.mapDerivedCategoryFactorsh.inv.app K))).mp
  have hf := comparisonFac RX RY G G square K
  simp only [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    homotopyCompInv, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at hf
  change (_ ≫ _) ≫ (blockDerivedComparison RX RY G G square).hom.app
    (DerivedCategory.Qh.obj K) ≫ dy.hom.app (G.rightDerivedFunctor.obj
      (DerivedCategory.Qh.obj K)) =
    (_ ≫ _) ≫ G.rightDerivedFunctor.map (dx.hom.app (DerivedCategory.Qh.obj K))
  simp only [Category.assoc]
  simp only [Category.assoc] at hf
  erw [Category.id_comp] at hf
  erw [reassoc_of% hf]
  have hy := dy.hom.naturality (G.rightDerivedFunctorUnit.app K)
  simp only [Functor.id_map] at hy
  erw [hy]
  have hey := exactIdentityFac RY ey ((G.mapHomotopyCategory (.up ℤ)).obj K)
  change RY.mapDerivedCategoryFactorsh.inv.app _ ≫ dy.hom.app _ = _ at hey
  have heyy := congrArg (fun f ↦
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory square.hom (.up ℤ)).app K) ≫
      f ≫ G.rightDerivedFunctorUnit.app K) hey
  simp only [Category.assoc] at heyy
  apply heyy.trans
  simp only [← G.rightDerivedFunctor.map_comp]
  have hex := exactIdentityFac RX ex K
  change RX.mapDerivedCategoryFactorsh.inv.app K ≫ dx.hom.app _ = _ at hex
  rw [hex]
  have hn := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory ex.hom (.up ℤ)).app K)
  simp only [Functor.comp_map] at hn
  erw [← hn]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  dsimp only [K]
  apply (HomotopyCategory.quotient Y (.up ℤ)).congr_map
  ext n
  exact coherent (I.X n)


end Identity

end WeilConjectures.SemilinearSections
