/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumCounitMaps
public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationPulledChartTransport
import WeilConjectures.AlgebraicGeometry.AffineTraceTowerCounitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
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
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.AlgebraicGeometry.VectorIntegrationBaseChangeCoordinates
import WeilConjectures.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import WeilConjectures.AlgebraicGeometry.VectorIntegrationCartesianWeightedTrace
import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumTensorCoefficient

import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Coefficient-weighted fibre trace in two coordinate blocks

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, simultaneous trivializations.
(blueprint: lem-pur-vector-integration-direct-sum-iterated-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Keep the existing named hd binder in the public statement.
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

attribute [local irreducible] AlgebraicGeometry.Etale.rightDerivedLowerShriek
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  AlgebraicGeometry.VectorBundleZeroSection.π AlgebraicGeometry.VectorBundleZeroSection.scheme
  AlgebraicGeometry.Etale.leftDerivedUpperStarComp
  AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local implicit_reducible] Scheme.Modules
  ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
  vectorIntegrationCoefficient vectorIntegrationSource
set_option maxRecDepth 4096
attribute [local irreducible] rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  vectorBundleIntegration vectorIntegrationGluing
  unboundedEtaleLowerShriekId affineLinearPullbackId
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensorSymmetry projectionMapOfCompactification

private theorem integration_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    VectorIntegrationNormalization N hN A hA S hS d F
      (vectorBundleIntegration N hN A hA S hS d F) := by
  unfold vectorBundleIntegration vectorIntegrationGluing
  exact (existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose_spec.2

private theorem pulled_integration_trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (T : Scheme.{u}) [IsNoetherian T] (a : T ⟶ V.toScheme) (j : T ⟶ S)
    (hj : j = a ≫ V.ι) :
    let := (vectorIntegration_geometry S d F).1
    let := (vectorIntegration_geometry S d F).2.1
    (ordinaryFinitePullback A j).map (vectorBundleIntegration N hN A hA S hS d F) ≫
        (ordinaryFiniteUnitPullback A j).hom =
      vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S d F)
        j (affineTracePullbackInvertible N j hS) d
        (affineTraceMap a d ≫ vectorIntegrationChart S d F V e)
        (vectorIntegrationPulledChart_isPullback S d F V e T a j hj)
        (affineLinearBaseCoefficient A N hA S d)
        (vectorIntegrationBaseCoefficientPullback A N hA t j hS d) ≫
      affineTraceCounit A N hA t D T (affineTracePullbackInvertible N j hS) d := by
  let := (vectorIntegration_geometry S d F).1
  let := (vectorIntegration_geometry S d F).2.1
  let := (vectorIntegration_geometry S d F).2.2
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let := affineTraceNoetherian T d
  let := affineTraceNoetherian V.toScheme d
  let k := vectorBundleIntegration N hN A hA S hS d F
  let hV := affineTracePullbackInvertible N V.ι hS
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a V.ι j hj).inv.naturality k
  have hu := ordinaryFiniteUnitPullback_comp A a V.ι j hj
  have hk := integration_normalization N hN A hA S hS d F t D V e
  have ht := vectorIntegration_pulled_chart_transport N hN A hA t S hS d F V e T a j hj
  have hb := affineTraceTowerCounit_baseChange A N hN hA t D
    (ordinaryFiniteP1BaseChange_of_normalization N hN A hA t D) a hV d
    (ordinaryFiniteUnit A V.toScheme)
  have hc := (affineTraceAdjunction A N hA t D T
    (affineTracePullbackInvertible N a hV) d).counit.naturality
      (ordinaryFiniteUnitPullback A a).hom
  dsimp only [ordinaryFinitePullback] at hn hu ht hk hb hc ⊢
  dsimp only [k] at hn
  simp only [Functor.comp_map, Functor.id_map] at hn hc
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a V.ι j hj).inv.app _)).mp
  try simp only [Category.assoc]
  rw [← reassoc_of% hn, ← hu, ← ht]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have hbc :
      affineTraceExchange A a d
          ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) ≫
        (affineTraceLeft A T d).map
          (affineTraceRightBaseChange A N hA t a hV d
            (ordinaryFiniteUnit A V.toScheme)).hom ≫
        (affineTraceLeft A T d).map
          ((affineTraceRight A N hA T d).map (ordinaryFiniteUnitPullback A a).hom) ≫
        affineTraceCounit A N hA t D T (affineTracePullbackInvertible N j hS) d =
      (ordinaryFinitePullback A a).map (affineTraceCounit A N hA t D V.toScheme hV d) ≫
        (ordinaryFiniteUnitPullback A a).hom := by
    dsimp only [ordinaryFinitePullback]
    unfold affineTraceCounit
    rw [hc, reassoc_of% hb]
  rw [hbc]
  have hh := congrArg (fun z ↦ (ordinaryFinitePullback A a).map z) hk
  dsimp only [vectorIntegrationLocalTrace, k, ordinaryFinitePullback] at hh ⊢
  simp only [Functor.map_comp] at hh
  rw [reassoc_of% hh]

private theorem restricted_integration_trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) :
    letI := (vectorIntegration_geometry S d F).1
    letI := (vectorIntegration_geometry S d F).2.1
    vectorIntegrationLocalTrace N hN A hA t D S hS d F W
        (VectorIntegrationDirectSumCounit.restrictedFrame hWV e) =
      vectorIntegrationCartesianPrefix N hN A hA t (VectorBundleZeroSection.π S d F)
        W.ι (affineTracePullbackInvertible N W.ι hS) d
        (vectorIntegrationRestrictedChart S d F W V hWV e)
        (vectorIntegrationRestrictedChart_isPullback S d F W V hWV e)
        (affineLinearBaseCoefficient A N hA S d)
        (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS d) ≫
      affineTraceCounit A N hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) d := by
  let := (vectorIntegration_geometry S d F).1
  let := (vectorIntegration_geometry S d F).2.1
  have hn := integration_normalization N hN A hA S hS d F t D W
    (VectorIntegrationDirectSumCounit.restrictedFrame hWV e)
  have ht := pulled_integration_trace N hN A hA t D S hS d F V e W.toScheme
    (S.homOfLE hWV) W.ι (S.homOfLE_ι hWV).symm
  exact hn.symm.trans ht

private theorem outer_integration_trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (s : ℕ)
    (G : S.Modules) [G.IsFiniteLocallyFreeOfRank s]
    (U : S.Opens) (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWU : W ≤ U)
    (M : DerivedCategoryModule A (VectorBundleZeroSection.scheme S s G))
    (k : M ⟶ vectorIntegrationCoefficient A N hA S s G) :
    letI := (vectorIntegration_geometry S s G).1
    letI := (vectorIntegration_geometry S s G).2.1
    (ordinaryFinitePullback A W.ι).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (VectorBundleZeroSection.π S s G)).map k) ≫
      vectorIntegrationLocalTrace N hN A hA t D S hS s G W
        (VectorIntegrationDirectSumCounit.restrictedFrame hWU eG) =
    (rightDerivedLowerShriekBaseChangeMap A
        (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)).app M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection W.toScheme s)).map
        ((ordinaryFinitePullback A
          (vectorIntegrationRestrictedChart S s G W U hWU eG)).map k ≫
          (vectorIntegrationCartesianCoefficient A N hA t
            (VectorBundleZeroSection.π S s G) W.ι
            (affineTracePullbackInvertible N W.ι hS) s
            (vectorIntegrationRestrictedChart S s G W U hWU eG)
            (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)
            (affineLinearBaseCoefficient A N hA S s)
            (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS s)).hom) ≫
      (affineLinearCompactComparison N hN A hA W.toScheme
        (affineTracePullbackInvertible N W.ι hS) s).inv ≫
      affineTraceCounit A N hA t D W.toScheme
        (affineTracePullbackInvertible N W.ι hS) s := by
  let := (vectorIntegration_geometry S s G).1
  let := (vectorIntegration_geometry S s G).2.1
  let := (vectorIntegration_geometry S s G).2.2
  let := affineTraceNoetherian W.toScheme s
  have hn := (rightDerivedLowerShriekBaseChangeMap A
    (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG)).naturality k
  rw [restricted_integration_trace N hN A hA t D S hS s G U eG W hWU]
  unfold vectorIntegrationCartesianPrefix
  dsimp only [ordinaryFinitePullback, vectorIntegrationCoefficient, Functor.comp_map] at hn ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private theorem tower_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : ℕ) : affineTraceMap (f ≫ g) d = affineTraceMap f d ≫ affineTraceMap g d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (AffineSpace.functor.obj (Opposite.op PUnit.{u + 1})).map
      (affineTraceMap (f ≫ g) d) = _
    rw [ih, Functor.map_comp]
    rfl

private theorem fibre_integration_trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U) :
    let E := VectorBundleZeroSection.scheme S s G
    let p := VectorBundleZeroSection.π S s G
    let F' := (Scheme.Modules.tensorPullback p).obj F
    let q := VectorBundleZeroSection.π E r F'
    let g := vectorIntegrationRestrictedChart S s G W U hWU eG
    let B := affineTraceTower W.toScheme s
    letI := (vectorIntegration_geometry S s G).2.2
    letI := (vectorIntegration_geometry E r F').1
    letI := (vectorIntegration_geometry E r F').2.1
    letI := affineTraceNoetherian W.toScheme s
    (ordinaryFinitePullback A g).map
        (vectorBundleIntegration N hN A hA E
          (affineTracePullbackInvertible N p hS) r F') ≫
        (ordinaryFiniteUnitPullback A g).hom =
      vectorIntegrationCartesianPrefix N hN A hA t q g
        (affineTracePullbackInvertible N g (affineTracePullbackInvertible N p hS)) r
        (VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU)
        (VectorIntegrationDirectSumCounit.chart_isPullback S r s F G V U eF eG W hWV hWU)
        (affineLinearBaseCoefficient A N hA E r)
        (vectorIntegrationBaseCoefficientPullback A N hA t g
          (affineTracePullbackInvertible N p hS) r) ≫
      affineTraceCounit A N hA t D B
        (affineTracePullbackInvertible N g (affineTracePullbackInvertible N p hS)) r := by
  let E := VectorBundleZeroSection.scheme S s G
  let p := VectorBundleZeroSection.π S s G
  let F' := (Scheme.Modules.tensorPullback p).obj F
  let q := VectorBundleZeroSection.π E r F'
  let g := vectorIntegrationRestrictedChart S s G W U hWU eG
  let B := affineTraceTower W.toScheme s
  let := (vectorIntegration_geometry S s G).1
  let := (vectorIntegration_geometry S s G).2.1
  let := (vectorIntegration_geometry S s G).2.2
  let := (vectorIntegration_geometry E r F').1
  let := (vectorIntegration_geometry E r F').2.1
  let := (vectorIntegration_geometry E r F').2.2
  let := affineTraceNoetherian W.toScheme s
  let := affineTraceNoetherian B r
  let O := p ⁻¹ᵁ W
  let e := VectorIntegrationDirectSumCounit.fibreOpenFrame S r s F G V eF W hWV
  let qs := affineTraceProjection W.toScheme s
  have hw : g ≫ p = qs ≫ W.ι :=
    (vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG).w
  let a : B ⟶ O.toScheme := (isPullback_morphismRestrict p W).lift qs g hw.symm
  have ha : a ≫ O.ι = g := (isPullback_morphismRestrict p W).lift_snd _ _ _
  let f : B ⟶ V.toScheme := qs ≫ S.homOfLE hWV
  have hf : g ≫ p = f ≫ V.ι := by
    dsimp only [f]
    rw [Category.assoc, S.homOfLE_ι]
    exact hw
  obtain ⟨H, hH⟩ := vectorIntegration_baseChange_coordinates p r F V eF O e B g a f ha hf
  let z := VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU
  let z' := affineTraceMap a r ≫ vectorIntegrationChart E r F' O e
  have hz : z' = affineTraceLinearMap B r H ≫ z := by
    apply (VectorTraceGeometry.baseChange_isPullback p r F).hom_ext
    · dsimp only [z']
      rw [hH]
      dsimp only [z, f]
      rw [Category.assoc, VectorIntegrationDirectSumCounit.chart_first]
      rw [tower_map_comp]
      simp only [vectorIntegrationRestrictedChart, Category.assoc, qs]
    · have hz' := (vectorIntegrationPulledChart_isPullback E r F' O e B a g ha.symm).w
      change z' ≫ q = (affineTraceLinearMap B r H ≫ z) ≫ q
      calc
        z' ≫ q = affineTraceProjection B r ≫ g := hz'
        _ = affineTraceLinearMap B r H ≫ affineTraceProjection B r ≫ g := by
          rw [← Category.assoc, affineTraceLinearMap_over]
        _ = (affineTraceLinearMap B r H ≫ z) ≫ q := by
          dsimp only [z, q, E, F', p]
          rw [Category.assoc, VectorIntegrationDirectSumCounit.chart_second]
  have ht := pulled_integration_trace N hN A hA t D E
    (affineTracePullbackInvertible N p hS) r F' O e B a g ha.symm
  obtain ⟨sqH, htrace⟩ := affineSpaceLinearTraceInvariance N hN A hA t D B
    (affineTracePullbackInvertible N g (affineTracePullbackInvertible N p hS)) r H
  have hact := vectorIntegrationCartesianPrefix_action N hN A hA t q g
    (affineTracePullbackInvertible N g (affineTracePullbackInvertible N p hS)) r z z'
    (VectorIntegrationDirectSumCounit.chart_isPullback S r s F G V U eF eG W hWV hWU)
    (vectorIntegrationPulledChart_isPullback E r F' O e B a g ha.symm)
    (affineTraceLinearMap B r H) sqH hz
    (affineLinearBaseCoefficient A N hA E r)
    (vectorIntegrationBaseCoefficientPullback A N hA t g
      (affineTracePullbackInvertible N p hS) r)
  dsimp only [q, z'] at hact
  dsimp only at ht
  rw [hact] at ht
  dsimp only [E, p, F', g, B, q, z] at ht htrace ⊢
  simpa only [Category.assoc, htrace] using ht

private theorem unit_comparison_eq
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCompactComparison N hN A hA S hS d =
      (affineTraceUnboundedCompactComparison A S d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  apply Iso.ext
  change (affineTracePlusCompatibility A S d).inv.app K ≫
    DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).hom.app K =
    (affineTraceUnboundedCompactComparison A S d).hom.app (DerivedCategory.Plus.ι.obj K)
  apply (cancel_epi ((affineTracePlusCompatibility A S d).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (affineTraceUnboundedCompactComparison_restriction A S d K).symm

/-- The projection-formula expression for successive bundle integrations has the
ordered two-block affine counit as its normal form. The base integration is replaced
by its prescribed local trace, and only
the fibre integration occurs. The sum-bundle integration and its product-presentation
transport are absent.
Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, tensor normalization of ordered affine counits.
(blueprint: lem-pur-vector-integration-direct-sum-iterated-counit).

Proof: Normalize vector-bundle integration on a frame using its defining gluing theorem.
Transport this normalization along the restricted chart, using the pulled-chart transport and
base change of the ordered affine counit; uniqueness of the normalized projective-line datum
allows the specified D. Naturality gives the outer G exchange formula. For the fibre bundle,
use fibreOpenFrame and Cartesian cancellation to identify its chart with the prescribed direct-sum
chart, up to an invertible linear action. Linear invariance of the affine trace removes this action.
Apply the Cartesian weighted-trace identity to the inner block. The ordered tensor-coefficient
identity identifies its source with the exact reference coefficient specified by hd. Exchange
naturality moves d into the inner shriek image. Finally, identify the bounded-below compact
comparison with the unbounded comparison at the unit, and use its naturality to move the inner
counit through the outer comparison. The counit of the composite adjunction is the r-block
counit followed by the s-block counit. This yields exactly the reference arrow. The identity
adjunction and tensor unit equations cover either rank zero, empty opens and zero coefficients.
-/
theorem vectorIntegration_directSum_iterated_counit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    [hP : IsIso (compactSupportProjectionMap A
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F))
      (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F))
      (vectorIntegrationCoefficient A N hA S s G))]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) [IsNoetherian W.toScheme] (hWV : W ≤ V) (hWU : W ≤ U) :
    let fibre :=
      (Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F;
    let q :=
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
      (fibre);
    let h :=
      q ≫ VectorBundleZeroSection.π S s G;
    let Wh :=
      (ordinaryFinitePullback A (h)).obj
      (affineLinearBaseCoefficient A N hA S (r + s));
    ∀ (d : Wh ≅
      ((ordinaryFiniteTensor A _).obj
        ((upperStar (ModuleCat.{u + 1} A) q).mapDerivedCategory.obj
          (vectorIntegrationCoefficient A N hA S s G))).obj
        (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r fibre))
      (hd : d =
      (ordinaryFinitePullback A (h)).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm r s)) ≪≫
          WeilConjectures.PurityFiniteSetting.purityPowerAdd A N hA S s r) ≪≫
      ordinaryFiniteTensorPullback A (h)
        (affineLinearBaseCoefficient A N hA S s) (affineLinearBaseCoefficient A N hA S r) ≪≫
      ordinaryFiniteTensorRightMapIso A _
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (q)
          (VectorBundleZeroSection.π S s G)).app _ ≪≫
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (q)).app (vectorIntegrationCoefficient A N hA S s G))
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (q)
          (VectorBundleZeroSection.π S s G)).app _ ≪≫
          (ordinaryFinitePullback A (q)).mapIso
            (vectorIntegrationBaseCoefficientPullback A N hA t
              (VectorBundleZeroSection.π S s G) hS r))),
    (ordinaryFinitePullback A W.ι).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S s G)).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (q)).map
          (d).hom ≫
        @inv _ _ _ _ (compactSupportProjectionMap A (q)
          (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r
            (fibre)) (vectorIntegrationCoefficient A N hA S s G)) hP ≫
        ((ordinaryFiniteTensor A _).obj (vectorIntegrationCoefficient A N hA S s G)).map
          (vectorBundleIntegration N hN A hA (VectorBundleZeroSection.scheme S s G)
            (affineTracePullbackInvertible N (VectorBundleZeroSection.π S s G) hS) r
            (fibre)) ≫
        (derivedTensorSingleUnitIso (vectorIntegrationCoefficient A N hA S s G)).hom)) ≫
      vectorIntegrationLocalTrace N hN A hA t D S hS s G W
        (VectorIntegrationDirectSumCounit.restrictedFrame hWU eG) =
    VectorIntegrationDirectSumCounit.counit N A hA t D S hS r s F G V U eF eG
      W hWV hWU := by
  dsimp only
  intro d hd
  let E := VectorBundleZeroSection.scheme S s G
  let p := VectorBundleZeroSection.π S s G
  let fibre := (Scheme.Modules.tensorPullback p).obj F
  let q := VectorBundleZeroSection.π E r fibre
  let h := q ≫ p
  let Wh := (ordinaryFinitePullback A h).obj
    (affineLinearBaseCoefficient A N hA S (r + s))
  let g := vectorIntegrationRestrictedChart S s G W U hWU eG
  let B := affineTraceTower W.toScheme s
  let qr := affineTraceProjection B r
  let qs := affineTraceProjection W.toScheme s
  let hW := affineTracePullbackInvertible N W.ι hS
  let hE := affineTracePullbackInvertible N p hS
  let hB := affineTracePullbackInvertible N g hE
  let := (vectorIntegration_geometry S s G).1
  let := (vectorIntegration_geometry S s G).2.1
  let := (vectorIntegration_geometry S s G).2.2
  let := (vectorIntegration_geometry E r fibre).1
  let := (vectorIntegration_geometry E r fibre).2.1
  let := (vectorIntegration_geometry E r fibre).2.2
  let := affineTraceNoetherian W.toScheme s
  let := affineTraceNoetherian B r
  let RsUnit := (affineTraceRight A N hA W.toScheme s).obj (ordinaryFiniteUnit A W.toScheme)
  let z := VectorIntegrationDirectSumCounit.chart S r s F G V U eF eG W hWV hWU
  let sq := VectorIntegrationDirectSumCounit.chart_isPullback S r s F G V U eF eG W hWV hWU
  let sqG := vectorIntegrationRestrictedChart_isPullback S s G W U hWU eG
  let cG := vectorIntegrationCartesianCoefficient A N hA t p W.ι hW s g sqG
    (affineLinearBaseCoefficient A N hA S s)
    (vectorIntegrationBaseCoefficientPullback A N hA t W.ι hS s)
  let c := VectorIntegrationDirectSumCounit.coefficient N A hA t S hS r s F G V U eF eG
    W hWV hWU
  let k := vectorBundleIntegration N hN A hA E hE r fibre
  let J := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map d.hom ≫
    @inv _ _ _ _ (compactSupportProjectionMap A q
      (vectorIntegrationCoefficient A N hA E r fibre)
      (vectorIntegrationCoefficient A N hA S s G)) hP ≫
    ((ordinaryFiniteTensor A E).obj (vectorIntegrationCoefficient A N hA S s G)).map k ≫
      (derivedTensorSingleUnitIso (vectorIntegrationCoefficient A N hA S s G)).hom
  have hk := fibre_integration_trace N hN A hA t D S hS r s F G V U eF eG W hWV hWU
  let hP' : IsIso (compactSupportProjectionMap A q
      ((ordinaryFinitePullback A q).obj (affineLinearBaseCoefficient A N hA E r))
      (vectorIntegrationCoefficient A N hA S s G)) := by
    simpa only [q, E, fibre, p, vectorIntegrationCoefficient] using hP
  have hw := vectorIntegrationCartesianWeightedTrace N hN A hA t D q g hB r z sq
    (affineLinearBaseCoefficient A N hA E r) (vectorIntegrationCoefficient A N hA S s G)
    RsUnit cG (vectorIntegrationBaseCoefficientPullback A N hA t g hE r) k hk
  have hc := vectorIntegrationDirectSumTensorCoefficient N A hA t S hS r s F G V U eF eG
    W hWV hWU d hd
  have hin : (ordinaryFinitePullback A g).map J ≫ cG.hom =
      (rightDerivedLowerShriekBaseChangeMap A sq).app Wh ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) qr).map c.hom ≫
        (affineTraceUnboundedCompactComparison A B r).inv.app
          ((affineTraceRight A N hA B r).obj RsUnit) ≫
        (affineTraceAdjunction A N hA t D B hB r).counit.app RsUnit := by
    have hn := (rightDerivedLowerShriekBaseChangeMap A sq).naturality d.hom
    dsimp only [J, vectorIntegrationCoefficient] at hw ⊢
    rw [Functor.map_comp, Category.assoc, hw]
    dsimp only [ordinaryFinitePullback, vectorIntegrationCoefficient, Functor.comp_map,
      Functor.id_map] at hn ⊢
    rw [reassoc_of% hn]
    rw [← Functor.map_comp_assoc]
    dsimp only [ordinaryFinitePullback, vectorIntegrationCoefficient] at hc
    rw [hc]
    rfl
  change (ordinaryFinitePullback A W.ι).map
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map J) ≫ _ = _
  rw [outer_integration_trace N hN A hA t D S hS s G U eG W hWU _ J]
  change (rightDerivedLowerShriekBaseChangeMap A sqG).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) qs).map
      ((ordinaryFinitePullback A g).map J ≫ cG.hom) ≫
      (affineLinearCompactComparison N hN A hA W.toScheme hW s).inv ≫
      affineTraceCounit A N hA t D W.toScheme hW s = _
  rw [hin, unit_comparison_eq N hN A hA W.toScheme hW s]
  have hn := (affineTraceUnboundedCompactComparison A W.toScheme s).inv.naturality
    ((affineTraceAdjunction A N hA t D B hB r).counit.app RsUnit)
  unfold VectorIntegrationDirectSumCounit.counit
  dsimp only [VectorIntegrationDirectSumCounit.blockAdjunction]
  rw [Adjunction.comp_counit_app]
  simp only [Functor.map_comp, Category.assoc, Iso.app_inv]
  rw [reassoc_of% hn]
  rfl


end AlgebraicGeometry.Etale
