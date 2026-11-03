/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorNormalizedTraceCartesian
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineVectorStandardFrame
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-! # Compact-support integration in an affine presentation

This equation concerns traces, before adjunction or restriction along a section.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Etale (purityTwistTransport)
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Modules
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  Etale.vectorBundleIntegration Etale.rightDerivedLowerShriek
  Etale.affineLinearBaseCoefficient Etale.upperStar Functor.leftDerivedFunctor
  Etale.leftDerivedUpperStarComp DerivedCategory.singleFunctors

-- Reuse the canonical derived-category instances already cached by finite pullback.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1
  Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3
  Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5
  Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7
  Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9
  Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11
  Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian Etale.leftDerivedUpperStarIsoMapDerivedCategory

private theorem pullback_identity_unit (A : Type (u + 1)) [CommRing A] (B : Scheme.{u}) :
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) (𝟙 B)).hom =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).hom.app (𝟙_ _) := by
  let H := Etale.ordinaryFinitePullback A (𝟙 B)
  let I := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B
  let c := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) (𝟙 B)
  let e := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (𝟙 B) (𝟙 B) (𝟙 B) (Category.id_comp _).symm
  have hc := Etale.leftDerivedUpperStarComp_hom_app_unit
    (ModuleCat.{u + 1} A) (𝟙 B) (𝟙 B) (𝟙 B) (Category.id_comp _).symm
  simp only [← Etale.leftDerivedUpperStarUnitIso_hom_eq_η] at hc
  have hc' : e.hom.app (𝟙_ _) ≫ H.map c.hom = 𝟙 _ := by
    apply (cancel_mono c.hom).mp
    simpa only [e, H, c, Etale.ordinaryFinitePullback, Category.assoc,
      Category.id_comp] using hc
  have hu := Etale.leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) (𝟙 B) (𝟙_ _)
  have hm : H.map c.hom = I.hom.app (H.obj (𝟙_ _)) := by
    apply (cancel_epi (e.hom.app (𝟙_ _))).mp
    exact hc'.trans hu.symm
  have hn := I.hom.naturality c.hom
  change H.map c.hom ≫ I.hom.app (𝟙_ _) = I.hom.app (H.obj (𝟙_ _)) ≫ c.hom at hn
  rw [hm] at hn
  exact ((cancel_epi (I.hom.app (H.obj (𝟙_ _)))).mp hn).symm

/-- A scheme isomorphism over the base identifies vector integration with the ordered
normalized affine trace. The isomorphism need not be linear or preserve zero.
Source: smooth-purity, Agreement on the model, translation and integration paragraphs;
vector integration in a frame and its zero-preserving Cartesian compatibility.
(blueprint: lem-pur-affine-vector-trace-presentation).

Proof: construct the canonical free rank-d bundle and its standard inverse global
frame k. The existing Cartesian vector-trace theorem applies to e.hom composed
with k without any zero-preserving assumption. Normalize the trace at that fixed
standard free frame. Compact-support exchange pasting and ordered coefficient
composition factor transport along e.hom composed with k into the transports
along k and e.hom. The transport along k is invertible, so cancellation gives
the assertion. Normalized twist transport is unique, and the standard-frame
normalization is quantified over every D. Naturality and the identity-pullback
unit law restore exactly the displayed unit comparison. Rank zero, the empty
base and zero coefficients use the same constructions and unit equations. -/
theorem affineVectorTracePresentation (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    let q := affineTraceProjection B d
    let π := VectorBundleZeroSection.π B d F
    letI := Dnc.compactifiable P q aB
    letI := Dnc.compactifiable P π aB
    ∀ (e : VectorBundleZeroSection.scheme B d F ≅ affineTraceTower B d)
      (we : e.hom ≫ q = π),
      let sq : IsPullback e.hom π q (𝟙 B) :=
        IsPullback.of_horiz_isIso ⟨we.trans (Category.comp_id _).symm⟩
      let c (T S : Scheme.{u}) (f : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) :=
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t f (P.diagonalExponent_isUnit aS) d
      let L := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) q
      let L' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π
      let τ := L.map
          ((Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
              P.diagonalExponent_annihilates t B (P.diagonalExponent_isUnit aB) d) ≪≫
            c _ _ q aB).inv ≫
        (Etale.affineLinearCompactComparison P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d).inv ≫
        Etale.affineTraceCounit P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t D B (P.diagonalExponent_isUnit aB) d ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
      let τ' := L'.map (c _ _ π aB).inv ≫
        Etale.vectorBundleIntegration P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
      (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq).app
          (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates (affineTraceTower B d) d) ≫
        L'.map (c _ _ e.hom (q ≫ aB)).hom ≫ τ' =
      (Etale.ordinaryFinitePullback P.Coefficient (𝟙 B)).map τ ≫
        (Etale.leftDerivedUpperStarUnitIso
          (ModuleCat.{u + 1} P.Coefficient) (𝟙 B)).hom := by
  have ht := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t
    (purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
  subst t
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B d F).2.2
  let F₀ := SheafOfModules.free (R := B.ringCatSheaf) (ULift.{u} (Fin d))
  let := (Etale.vectorIntegration_geometry B d F₀).1
  let := (Etale.vectorIntegration_geometry B d F₀).2.1
  let := (Etale.vectorIntegration_geometry B d F₀).2.2
  let := affineTraceNoetherian B d
  let q := affineTraceProjection B d
  let π := VectorBundleZeroSection.π B d F
  let π₀ := VectorBundleZeroSection.π B d F₀
  let := Dnc.compactifiable P q aB
  let := Dnc.compactifiable P π aB
  let := Dnc.compactifiable P π₀ aB
  extract_lets c L L' τ τ'
  intro e we
  extract_lets sq
  let k := affineVectorStandardChart B d
  let sk := affineVectorStandardChart_square B d
  have sv : IsPullback (e.hom ≫ k) π π₀ (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.assoc, affineVectorStandardChart_over, we, Category.comp_id]⟩
  let tw := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  have hc := Etale.affineVectorTraceAction_comp P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw π₀ q π k e.hom sk sq sv
    (P.diagonalExponent_isUnit (π₀ ≫ aB)) (P.diagonalExponent_isUnit (q ≫ aB)) d
  have hv := OrientationRefinement.finite_trace_cartesian P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
    B B (P.diagonalExponent_isUnit aB) (P.diagonalExponent_isUnit aB)
    d F₀ F (𝟙 B) (e.hom ≫ k) sv (P.diagonalExponent_isUnit (π₀ ≫ aB))
  have h₀ := affineVectorStandardFrame P B aB d tw D
  have hv' := congrArg (fun z ↦
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫ z) hv
  dsimp only at hv' h₀
  have h : Etale.affineVectorTraceAction P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates tw π₀ π (e.hom ≫ k) sv
      (P.diagonalExponent_isUnit (π₀ ≫ aB)) d ≫ τ' =
      Etale.affineVectorTraceAction P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates tw π₀ q k sk
        (P.diagonalExponent_isUnit (π₀ ≫ aB)) d ≫ τ := by
    simpa only [Etale.affineVectorTraceAction, τ', τ, L', L, c, Category.assoc] using
      hv'.trans h₀.symm
  rw [← hc, Category.assoc] at h
  have : IsIso (Etale.affineVectorTraceAction P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates tw π₀ q k sk
      (P.diagonalExponent_isUnit (π₀ ≫ aB)) d) := by
    have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sk
    dsimp only [Etale.affineVectorTraceAction]
    infer_instance
  have he := (cancel_epi (Etale.affineVectorTraceAction P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw π₀ q k sk
    (P.diagonalExponent_isUnit (π₀ ≫ aB)) d)).mp h
  have he' := congrArg (fun z ↦
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).hom.app _ ≫ z) he
  simp only [Etale.affineVectorTraceAction, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp] at he'
  rw [pullback_identity_unit]
  have hn :=
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).hom.naturality τ
  dsimp only [Functor.id_map, Etale.ordinaryFinitePullback] at hn ⊢
  rw [hn]
  simpa only [Category.assoc, L', c] using he'

end WeilConjectures.PurityFiniteSetting
