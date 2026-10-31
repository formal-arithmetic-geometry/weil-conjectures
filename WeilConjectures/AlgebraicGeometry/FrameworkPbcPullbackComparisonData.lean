/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FdPullbackComparison
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackShiftCoordinates

/-! # Framework and PBC pullback and scalar comparison

Source: smooth-purity, purity-transport coefficient-change proof; Stacks 099N,
0941, 07A4 and 0D6D (blueprint: def-pur-framework-pbc-pullback-comparison-data).
The comparisons retain the strict quotient tower, its augmentation, the ordinary
balanced tensor maps, the canonical completion units and raw rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genCtorIdx false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The chain-level normalization of inverse pi: ordinary pullback maps into the
realization of its strict finite quotient tower, with zero shifted coordinate.
Source: Stacks 099N(5), 0941
(blueprint: def-pur-framework-pbc-pullback-comparison-data). -/
structure PullbackChain {X Y : Scheme.{u}} (h : X ⟶ Y) where
  map :
    (fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ) ⋙
        (pbcActualModulePull h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⟶
      integralOperationsPullbackComplexFunctor l E h ⋙
        (fdCoefficientTransport l E X).mapHomologicalComplex (.up ℤ)
  quotients : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (n : ℕ) (V : Y.ProEt) (x : (P.X i).val.obj (op V))
    (x' : ((fdCoefficientTransport l E Y).obj (P.X i)).val.obj (op V)), HEq x' x →
    HEq (((map.app P).f i ≫ (fdCoefficientTransport l E X).map
        ((CochainComplex.mappingCocone.fst
          (IntegralCompletedComparison.roosEnd l E h P)).f i ≫
          (Pi.π (fun k : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj
            (op k)) n).f i)).val.app (op ((proEtaleBaseChange h).obj V))
      (pbcActualModuleUnitSection h (pbcIntegralDatum l E)
        ((fdCoefficientTransport l E Y).obj (P.X i)) V x'))
      (integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (coefficientIntegralScalarUnitSection l E Y n (P.X i) (op V) x))
  shifted : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
    (map.app P).f i ≫ (fdCoefficientTransport l E X).map
      ((CochainComplex.mappingCocone.snd
        (IntegralCompletedComparison.roosEnd l E h P)).v i (i - 1) (by omega)) = 0

/-- One normalized pullback isomorphism on the full constructible domain. The
normalization is a whole-chain identity, not a test on separate derived reductions.
Source: Stacks 099N(5), 0941
(blueprint: def-pur-framework-pbc-pullback-comparison-data). -/
structure Pullback {X Y : Scheme.{u}} (h : X ⟶ Y) where
  chain : PullbackChain l E h
  pi : (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E h ⋙
        integralDetailedTransport X l E ≅
      (sfIntegralConstructible l E Y).ι ⋙ integralDetailedTransport Y l E ⋙
        pbcActualCompletedPull h (pbcIntegralDatum l E)
  normalization : ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj)),
    (pbcActualCompletedPullUnit h (pbcIntegralDatum l E)).app
        ((integralDetailedTransport Y l E).obj (DerivedCategory.Q.obj P.obj)) ≫
      pi.inv.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport X l E).map
        ((integralDerivedPullbackComparison l E h).hom.app P) ≫
      (fdCoefficientTransportFactors l E X).hom.app
        ((integralOperationsPullbackComplexFunctor l E h).obj P.obj) =
    (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
        ((fdCoefficientTransportFactors l E Y).hom.app P.obj) ≫
      pbcActualPullComplexCounit h (pbcIntegralDatum l E)
        (((fdCoefficientTransport l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map (chain.map.app P.obj)


end WeilConjectures.FrameworkPbc
