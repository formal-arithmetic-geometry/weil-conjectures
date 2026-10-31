/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalarSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem

/-!
# Normalized systems of ordinary supported Cartier Kummer maps

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(blueprint: def-asd-ordinary-supported-kummer-system).

## Main definitions

* `supportedDerivedUnit`: the canonical derived unit.
* `supportedExactDerivedMap`: the existing exact-functor/Ext comparison in general form.
* `OrdinarySupportedKummerSystem`: relative, Chern, pullback and scalar normalizations.
* The class families and compatibility predicates keep the dependent fields compact.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vC vD uC uD wC wD wE

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Match the category-instance proofs captured in the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2


/-- The classes interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
def SupportedKummerClassFamily (N : ℕ) : Type (u + 2) :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hT : IsUnit (N : Γ(T, ⊤))),
    Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2

/-- The relative interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
@[irreducible]
def SupportedKummerRelative (N : ℕ)
    (classes : SupportedKummerClassFamily.{u} N) : Prop :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))),
    SupportedKummerBoundary A N hA i hI hT (classes A hA i hI hT)

/-- The firstChern interface, represented by Ext through the canonical `Ext.homEquiv`.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
def SupportedKummerChernFamily (N : ℕ) : Type (u + 2) :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hT : IsUnit (N : Γ(T, ⊤))),
    Ext (ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2

/-- The firstChern_normalization interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
@[irreducible]
def SupportedKummerFirstChernNormalization (N : ℕ)
    (firstChern : SupportedKummerChernFamily.{u} N) : Prop :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))),
    (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
      ((firstChern A hA i hI hT).mapExactFunctor (RawModuleScalarComparison.forget A T))
      (zero_add 2) = supportedKummerChern A N hA i hI hT

/-- The chern interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
@[irreducible]
def SupportedKummerChernCompatibility (N : ℕ)
    (classes : SupportedKummerClassFamily.{u} N)
    (firstChern : SupportedKummerChernFamily.{u} N) : Prop :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))),
    (Ext.mk₀ (supportedConstantUnit A i)).comp
      (classes A hA i hI hT) (zero_add 2) = firstChern A hA i hI hT

/-- The transport interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
def SupportedKummerTransportFamily (N : ℕ) : Type (u + 2) :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0),
    OrdinaryFiniteTwistTransport A N hA

/-- The base_change interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
@[irreducible]
def SupportedKummerBaseChange (N : ℕ)
    (classes : SupportedKummerClassFamily.{u} N)
    (transport : SupportedKummerTransportFamily.{u} N) : Prop :=
  ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    [IsClosedImmersion i] [IsClosedImmersion i'] (v : T' ⟶ T) (w : D' ⟶ D)
    (sq : IsPullback w i' i v) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))),
    IsIso (supportedConstantExchange A i i' v w sq.toCommSq) ∧
    (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp
        (classes A hA i' hI' hT') (zero_add 2) =
      ((classes A hA i hI hT).mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
        (Ext.mk₀ ((transport A hA).line v hT).hom) (add_zero 2)

/-- The scalar interface of the supported Kummer system.
Source: Stacks 03PL, 0A45 (blueprint: def-asd-ordinary-supported-kummer-system). -/
@[irreducible]
def SupportedKummerScalarCompatibility (N : ℕ)
    (classes : SupportedKummerClassFamily.{u} N) : Prop :=
  ∀ [NeZero N] (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))),
    SupportedKummerScalar
      ((Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom) N
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N)) (ZMod.natCast_self N)) hA i
      (classes (ULift.{u + 1} (ZMod N))
        (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N)) (ZMod.natCast_self N)) i hI hT)
      (classes A hA i hI hT)

/-- All ordinary supported Kummer maps, normalized by their relative torsor boundaries.
The finite-ring family is simultaneous so that arbitrary Cartier-preserving pullback
and change of coefficients are actual equalities between its members. The Chern clause
is the unit equation in Ext: the canonical exact-direct-image comparison identifies
this with composition of `supportedDerivedUnit` and the exact derived realization.
Source: Stacks 03PL, 0A45; blueprint lem-amb-cartier-kummer-map
(blueprint: def-asd-ordinary-supported-kummer-system). -/
def OrdinarySupportedKummerSystem (N : ℕ) : Type (u + 2) :=
  { data : SupportedKummerClassFamily.{u} N ×
      SupportedKummerChernFamily.{u} N × SupportedKummerTransportFamily.{u} N //
    SupportedKummerRelative N data.1 ∧
    SupportedKummerFirstChernNormalization N data.2.1 ∧
    SupportedKummerChernCompatibility N data.1 data.2.1 ∧
    SupportedKummerBaseChange N data.1 data.2.2 ∧
    SupportedKummerScalarCompatibility N data.1 }


end AlgebraicGeometry.Etale
