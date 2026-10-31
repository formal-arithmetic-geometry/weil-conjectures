/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedToposDerivedAdjunctionOfUniverses
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
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientClosedTensorComparison
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Tensor comparison for a supplied derived pullback in independent universes

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-weil-pbc-ringed-tensor-comparison-independent).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u wX wY
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor WeilConjectures
open SheafOfModules MonoidalCategory
namespace CategoryTheory

set_option maxHeartbeats 800000 in
-- Representative descent composes the ordinary and derived comparison isomorphisms.
/-- A left adjoint to the supplied derived module direct image preserves the derived
 tensor bifunctor, with independent localization universes and arbitrary closed tensor models.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-weil-pbc-ringed-tensor-comparison-independent).

Proof: construct the ordinary pullback as algebraic inverse image followed by scalar
extension. Uniqueness of ordinary and derived left adjoints identifies it, on K-flat
flat-term representatives, with the supplied L. On those representatives compose the
ordinary total-tensor comparison with the representative tensor isomorphisms on the
two sites. Their restrictions determine natural transformations fully faithfully,
so the comparison descends to a natural isomorphism on the two derived categories.
The closed tensor comparison transports it to the supplied closed structures.
-/
theorem ringed_tensor_comparison_independent
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (L : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wX} RX)
    (a : L ⊣ Rf)
    (SY : CoefficientClosedStructure (derivedInternalHom.{u, wY} J RY))
    (SX : CoefficientClosedStructure (derivedInternalHom.{u, wX} K RX)) :
    Nonempty (SY.tensor ⋙ L ≅ (L.prod L) ⋙ SX.tensor) := by
  classical
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)
  let B := ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
  let := f.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image J K f.inverse f.direct f.adj RY
  obtain ⟨c, hc⟩ := structural_map K J RX RY f RI I
  let F := I.modules ⋙ SheafOfModules.tensorFunctor c
  obtain ⟨adjF⟩ : Nonempty (F ⊣ f.modules) := supplied_adjunction f RI I c hc
  let _ : PreservesColimits F := adjF.leftAdjoint_preservesColimits
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let _ : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hobj (M : A) : F.obj M = changeOfRings c (I.modules.obj M) := rfl
  have hmap {M N : A} (g : M ⟶ N) : F.map g = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map g) ≫ eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨L0, ⟨adj0⟩, G, ⟨adjG⟩, hG, ε, hε, he⟩ :=
    f.exists_derivedLeftAdjoint RY RX Rf ρ hRf hCompute
  let := hG
  let eL := a.leftAdjointUniq adj0
  let eG := adjG.leftAdjointUniq adjF
  let π := HomotopyCategory.quotient A (.up ℤ)
  let εc : DerivedCategory.Q.{wY} ⋙ L0 ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{wX} :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv L0 ≫
      Functor.whiskerLeft π ε ≫
      Functor.whiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso B).hom
  let eps : DerivedCategory.Q.{wY} ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{wX} :=
    Functor.whiskerLeft DerivedCategory.Q eL.hom ≫ εc ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex eG (.up ℤ)).hom DerivedCategory.Q
  let PY := cochainTensorFlatRepresentatives J RY
  let PX := cochainTensorFlatRepresentatives K RX
  have heps (P : CochainComplex A ℤ) (hp : PY P) : IsIso (eps.app P) := by
    have hflat : ∀ n : ℤ, (P.X n).IsFlat :=
      fun n ↦ (flat_iff_flatOnSite (P.X n)).2 (hp.2 n)
    have := he P ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hp.1) hflat
    dsimp only [eps, εc, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    infer_instance
  have hF (P : CochainComplex A ℤ) (hp : PY P) :
      PX ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    exact isKFlat_ringedToposPullback f.inverse f.direct f.adj I c F hobj hmap P hp.1 hp.2
  obtain ⟨SY0, TY, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, wY} J RY
  obtain ⟨SX0, TX, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, wX} K RX
  let iy := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := RY) :
      ObjectProperty (CochainComplex A ℤ)) PY.ι (fun P ↦ P.property.1)
  let ix := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (J := K) (R := RX) :
      ObjectProperty (CochainComplex B ℤ)) PX.ι (fun P ↦ P.property.1)
  let qY := PY.ι ⋙ DerivedCategory.Q.{wY}
  let qX := PX.ι ⋙ DerivedCategory.Q.{wX}
  let tY := coefficientTotalTensor.{u, u, u} J RY
  let tX := coefficientTotalTensor.{u, u, u} K RX
  let rY : (PY.ι.prod PY.ι) ⋙ tY ⋙ DerivedCategory.Q.{wY} ≅
      (qY.prod qY) ⋙ SY.tensor :=
    Functor.isoWhiskerLeft (iy.prod iy) TY.comparison ≪≫
      Functor.isoWhiskerLeft (qY.prod qY) (SY0.comparison SY)
  let rX : (PX.ι.prod PX.ι) ⋙ tX ⋙ DerivedCategory.Q.{wX} ≅
      (qX.prod qX) ⋙ SX.tensor :=
    Functor.isoWhiskerLeft (ix.prod ix) TX.comparison ≪≫
      Functor.isoWhiskerLeft (qX.prod qX) (SX0.comparison SX)
  obtain ⟨_, _, _, hff⟩ := (cochain_tensor_model_rigidity.{u, u, u, wY,
    u + 1, wX} J RY)
  let W := (whiskeringLeft _ _ (ringedSiteDerived.{u, wX} RX)).obj (qY.prod qY)
  have ff : W.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective W).2
      (hff _ inferInstance)).some
  obtain ⟨⟨k⟩, _⟩ := canonicalRingedTensorComparison_existsUnique
    RY RX RI f.inverse I c F hobj f.direct f.adj hmap
  let b0 : ((F.mapHomologicalComplex (.up ℤ)).prod
      (F.mapHomologicalComplex (.up ℤ))) ⋙ tX ≅ tY ⋙ F.mapHomologicalComplex (.up ℤ) :=
    NatIso.ofComponents
      (fun P ↦ k.totalIso RY RX RI f.inverse I c F hobj f.modules adjF P.1 P.2)
      (by
        intro P Q g
        let := monoidalCategory RY
        let := monoidalCategory RX
        let := ringedTensorPreadditive RY
        let := ringedTensorPreadditive RX
        dsimp only [tX, tY, coefficientTotalTensor, Functor.comp_map, Functor.prod_map,
          CanonicalRingedTensorComparison.totalIso, CanonicalRingedTensorComparison.total]
        simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
          asIso_hom, CanonicalTensorPullbackProof.tensorMap_factor]
        exact CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
          F k.mu k.naturality g.1 g.2)
  have het (P Q : CochainComplex A ℤ) (hp : PY P) (hq : PY Q) :
      IsIso (eps.app (tY.obj (P, Q))) := by
    have ht := KFlatTotalTensorModel.kFlat_total_tensor_model RY P Q
      hp.1 hq.1 hp.2 hq.2
    exact heps _ ⟨ht.1, ht.2.1⟩
  obtain ⟨α, _, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q (F.mapHomologicalComplex (.up ℤ)) L eps
    PY PX hF ff tY tX SY.tensor SX.tensor rY rX b0.symm heps het
  exact ⟨α⟩

end CategoryTheory
