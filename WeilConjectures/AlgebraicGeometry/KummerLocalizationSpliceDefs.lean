/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.SmoothPurity.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern

/-! # Concrete Kummer and localization splice models
Source: Stacks Tags 03PL and 0A45; the finite Cartier principal chart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The ordinary module Ext representative of the scalar Kummer boundary of a unit.
Source: Stacks 03PL (blueprint: def-pur-kummer-localization-splice-models). -/
def finiteKummerUnitClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 1 :=
  (ordinaryFiniteExtHomEquiv A T _ _ 1).symm
    ((ordinaryFiniteClassEquiv A T _ 1).symm
      (Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 1
        (T.kummerδ₀ N hT (Additive.ofMul s))))


/-- Extension by zero of the Kummer class, followed by the normalized twist counit.
Source: Stacks 03PL and 0A45 (blueprint: def-pur-kummer-localization-splice-models). -/
def finiteKummerOpenClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (T : Scheme.{u}) (W : T.Opens) (hT : IsUnit (N : Γ(T, ⊤)))
    (s : Γ(W.toScheme, ⊤)ˣ) :
    Ext ((openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι).obj
      ((upperStar (ModuleCat.{u + 1} A) W.ι).obj (ordinaryFiniteConstant A T)))
      (Scheme.finiteEtaleTateLine T N A hA) 1 :=
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) W.ι
  let hW : IsUnit (N : Γ(W.toScheme, ⊤)) := by simpa using hT.map W.ι.appTop.hom
  let ε := J.map (t.line W.ι hT).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) W.ι).counit.app
      (Scheme.finiteEtaleTateLine T N A hA)
  (Ext.mk₀ (J.map ((Scheme.upperStarConstantSheafIso
    (ModuleCat.{u + 1} A) W.ι).app (ModuleCat.of A A)).hom)).comp
      (((finiteKummerUnitClass A N hA W.toScheme hW s).mapExactFunctor J).comp
        (Ext.mk₀ ε) (add_zero 1)) (zero_add 1)

/-- The coefficient localization boundary as an actual open-closed Yoneda splice.
Source: Stacks 0A45 (blueprint: def-pur-kummer-localization-splice-models). -/
def finiteKummerLocalizationBoundary (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (hT : IsUnit (N : Γ(T, ⊤))) (s : Γ(W.toScheme, ⊤)ˣ) :
    Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2 :=
  (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} A) i).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).inv)).comp
        ((shortExact_openClosedShortComplex (ModuleCat.{u + 1} A) W.ι i
          (ordinaryFiniteConstant A T) h).extClass.comp
            (finiteKummerOpenClass A N hA t T W hT s) (rfl : 1 + 1 = 2)) (zero_add 2)

/-- The integral degree-one boundary, with the closed constant comparison included.
Source: Stacks 0A45 (blueprint: def-pur-kummer-localization-splice-models). -/
def integralLocalizationBoundary (C : PrincipalTorsorComparisons.{u})
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (g : T.gmSheaf.obj.obj (op (Scheme.Etale.mk W.ι))) :
    Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      T.gmSheaf 1 :=
  (Ext.mk₀ ((lowerStar AddCommGrpCat.{u + 1} i).map
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).comp
        ((shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} W.ι i
          (supportedIntegralConstant T) h).extClass.comp
            (Ext.mk₀ ((C.openSection T D i W h T.gmSheaf).symm g)) (add_zero 1))
        (zero_add 1)


end AlgebraicGeometry.Etale
