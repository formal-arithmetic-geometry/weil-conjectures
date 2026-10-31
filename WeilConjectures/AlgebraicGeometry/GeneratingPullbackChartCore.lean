/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeneratingPullbackChartGeometry
import WeilConjectures.AlgebraicGeometry.GeneratingPullbackChartModuleComparison
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
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
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! The geometric and module data underlying a generating pullback chart.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4.
(blueprint: lem-weil-pbc-generating-pullback-chart-core).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Pullback chart data before the target ideal generators are transported.
Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4.
(blueprint: lem-weil-pbc-generating-pullback-chart-core). -/
structure PullbackCechChartCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (u : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) where
  U : D
  V : C
  r : ℕ
  b : Fin r → RY.obj.obj (op V)
  morphism : RingedToposMorphism
    ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V))
  F : ringedSiteModules.{u}
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V)) ⥤
    ringedSiteModules.{u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
  additive : F.Additive
  adjunction : F ⊣ morphism.modules
  ringIso : F.obj (SheafOfModules.unit
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V))) ≅
    SheafOfModules.unit ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
  comparison : SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) V ⋙ F ≅
    G ⋙ SheafOfModules.overFunctor.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) U
  ring_compatibility :
    F.map (ringedOverRingIso RY V).hom ≫ ringIso.hom =
      comparison.hom.app (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
        (SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) U).map u.hom ≫
          (ringedOverRingIso RX U).hom

/-- A section of an inverse-image representable supplies the core chart data.
The proof is the object-slice relocalization of the geometric ringed pullback and
its module adjunction; the result records only the data needed before generator
transport. Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4;
algebraization.tex, Tags 099E and 0A0G.
(blueprint: lem-weil-pbc-generating-pullback-chart-core).
-/
theorem exists_generating_pullback_chart_core
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (G : ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [G.PreservesZeroMorphisms]
    (hG : G ⊣ f.modules)
    (u : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (U : D) (V : C) (r : ℕ) (b : Fin r → RY.obj.obj (op V))
    (s : (f.inverse.obj
      ((presheafToSheaf J (Type u)).obj (yoneda.obj V))).obj.obj (op U)) :
    ∃ t : PullbackCechChartCore RY RX G u,
      t.U = U ∧ t.V = V ∧ t.r = r ∧ HEq t.b b := by
  obtain ⟨chart⟩ := exists_object_slice_ringed_chart RY RX f U V s
  let _ : PreservesFiniteLimits chart.morphism.inverse := chart.morphism.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image (J.over V) (K.over U)
    chart.morphism.inverse chart.morphism.direct chart.morphism.adj (RY.over V)
  obtain ⟨c, hc⟩ := structural_map (K.over U) (J.over V)
    (RX.over U) (RY.over V) chart.morphism RI I
  let F := I.modules ⋙ SheafOfModules.tensorFunctor c
  obtain ⟨adj⟩ : Nonempty (F ⊣ chart.morphism.modules) :=
    supplied_adjunction chart.morphism RI I c hc
  let _ : PreservesColimits F := adj.leftAdjoint_preservesColimits
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let hF : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  obtain ⟨comparison⟩ := object_slice_module_comparison RY RX f U V chart G hG F adj
  let ringIso : F.obj (SheafOfModules.unit
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V))) ≅
      SheafOfModules.unit
        ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)) :=
    comparison.app (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≪≫
      (SheafOfModules.overFunctor
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) U).mapIso u
  refine ⟨{
    U := U
    V := V
    r := r
    b := b
    morphism := chart.morphism
    F := F
    additive := hF
    adjunction := adj
    ringIso := ringIso
    comparison := comparison
    ring_compatibility := ?_
  }, rfl, rfl, rfl, HEq.rfl⟩
  simp only [ringedOverRingIso, Functor.map_id, Category.id_comp, Category.comp_id,
    ringIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.refl_hom]

end CategoryTheory
