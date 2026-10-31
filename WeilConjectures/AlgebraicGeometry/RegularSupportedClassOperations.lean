/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
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
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-! # Canonical operations on ordinary supported etale classes

Source: ILO, Expose XVI 2.1--2.3 and 3.2--3.3; Stacks Project, Tag 03Q6
(blueprint: def-per-regular-supported-class-operations).

Ext realizations, Tate multiplication, the projection-formula composition square,
and canonical restriction equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

/-- Supported etale cohomology, in its ordinary Ext realization.
Source: ILO XVI 2.1; Stacks 03Q6 (blueprint: def-per-regular-supported-class-operations). -/
abbrev regularSupportedCohomology (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {Z X : Scheme.{u}} (i : Z ⟶ X) (a : ℤ) (q : ℕ) :=
  Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A Z))
    (Scheme.finiteEtaleTateSheaf A m X hA a) q

/-- A supported cohomology class, with no exceptional-functor or purity assumption.
Source: ILO XVI 2.3.1 (blueprint: def-per-regular-supported-class-operations). -/
abbrev RegularSupportedClass (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {Z X : Scheme.{u}} (i : Z ⟶ X) (c : ℕ) :=
  regularSupportedCohomology A m hA i c (2 * c)

/-- The corresponding supported derived morphism. Adjunction gives the eta of the node.
Source: ILO XVI 2.3.1 (blueprint: def-per-regular-supported-class-operations). -/
def regularClassRealization (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : ℕ) (gamma : RegularSupportedClass A m hA i c) :
    (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A Z) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA c))⟦((2 * c : ℕ) : ℤ)⟧ :=
  ((lowerStar (ModuleCat.{u + 1} A) i).singleFunctorCompRightDerivedFunctorIso.app
    (ordinaryFiniteConstant A Z)).hom ≫ gamma.hom

attribute [local irreducible] regularClassRealization

/-- Addition of the Tate degrees and even shifts, through the existing tensor comparison.
Source: ILO XVI 2.3.2 (blueprint: def-per-regular-supported-class-operations). -/
def regularClassMultiply (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Scheme.FiniteEtaleTwistPullbackData A m hA) (X : Scheme.{u})
    (hX : IsUnit (m : Γ(X, ⊤))) (a b : ℕ) :
    (((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA a))⟦((2 * a : ℕ) : ℤ)⟧ ⊗
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA b))⟦((2 * b : ℕ) : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA (b + a)))⟦((2 * (b + a) : ℕ) : ℤ)⟧ :=
  (derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _
    ((2 * a : ℕ) : ℤ) ((2 * b : ℕ) : ℤ)).hom ≫
    (shiftFunctor _ (((2 * a : ℕ) : ℤ) + ((2 * b : ℕ) : ℤ))).map
      ((singleFunctorObjTensorIso
        (Scheme.finiteEtaleTateSheaf A m X hA a)
        (Scheme.finiteEtaleTateSheaf A m X hA b)
        (ObjectProperty.flat_of_tensorIso
          (t.p X hX a (-(a : ℤ)) ≪≫ eqToIso (congrArg
            (Scheme.finiteEtaleTateSheaf A m X hA) (add_neg_cancel (a : ℤ))) ≪≫
            eqToIso (by rfl)))).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((t.p X hX a b).hom ≫ eqToHom (congrArg
            (Scheme.finiteEtaleTateSheaf A m X hA)
            (by omega : (a : ℤ) + (b : ℤ) = ((b + a : ℕ) : ℤ))))) ≫
    (eqToIso (congrArg (fun q : ℤ ↦
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA (b + a)))⟦q⟧)
      (by omega : ((2 * a : ℕ) : ℤ) + ((2 * b : ℕ) : ℤ) =
        ((2 * (b + a) : ℕ) : ℤ)))).hom

attribute [local irreducible] regularClassMultiply

/-- Inverse image of the shifted Tate object, using the recorded normalized comparisons.
Source: ILO XVI 2.2.3.1 (blueprint: def-per-regular-supported-class-operations). -/
def regularClassTargetPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Y X : Scheme.{u}} (v : Y ⟶ X)
    (hX : IsUnit (m : Γ(X, ⊤))) (hY : IsUnit (m : Γ(Y, ⊤))) (c : ℕ) :
    (ordinaryFinitePullback A v).obj
      (((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA c))⟦((2 * c : ℕ) : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m Y hA c))⟦((2 * c : ℕ) : ℤ)⟧ :=
  letI : (ordinaryFinitePullback A v).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) v
  ((ordinaryFinitePullback A v).commShiftIso ((2 * c : ℕ) : ℤ)).app _ ≪≫
    (shiftFunctor _ ((2 * c : ℕ) : ℤ)).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (t.c v hX hY c))

attribute [local irreducible] regularClassTargetPullback

/-- The canonical supported product, specified by its projection-formula square.
This is exactly exceptional composition after transposition, and fixes the intermediate
arrow on the whole source of the supported action.
Source: ILO XVI 2.3.2 (blueprint: def-per-regular-supported-class-operations). -/
def RegularClassComposition (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hX : IsUnit (m : Γ(X, ⊤))) (hY : IsUnit (m : Γ(Y, ⊤))) (a b : ℕ)
    (alpha : RegularSupportedClass A m hA i a)
    (beta : RegularSupportedClass A m hA j b)
    (gamma : RegularSupportedClass A m hA (i ≫ j) (a + b)) : Prop :=
  ∃ delta : (ordinaryFinitePushforward A j).obj
      (((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m Y hA a))⟦((2 * a : ℕ) : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A m X hA (a + b)))⟦((2 * (a + b) : ℕ) : ℤ)⟧,
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
        (ordinaryFiniteUnit A Y)).app _ ≫
      (ordinaryFinitePushforward A j).map
        (tensorHom (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom
          (regularClassTargetPullback A m hA t j hX hY a).hom ≫ (λ_ _).hom) ≫ delta =
      tensorHom (regularClassRealization A m hA j b beta) (𝟙 _) ≫
        regularClassMultiply A m hA t X hX b a ∧
    regularClassRealization A m hA (i ≫ j) (a + b) gamma =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) i j).inv.app
        (ordinaryFiniteUnit A Z) ≫
      (ordinaryFinitePushforward A j).map (regularClassRealization A m hA i a alpha) ≫ delta

/-- The graph of the canonical restriction on supported cohomology.
The closed constant exchange is an isomorphism for a Cartesian closed pair. Thus
this equation specifies the comparison itself, without choosing an arbitrary map.
Source: ILO XVI 2.2.3.1; Stacks 03Q6
(blueprint: def-per-regular-supported-class-operations). -/
def RegularSupportedRestriction (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : IsPullback w i' i v)
    (hX : IsUnit (m : Γ(X, ⊤))) (hX' : IsUnit (m : Γ(X', ⊤))) (a : ℤ) (q : ℕ)
    (x : regularSupportedCohomology A m hA i a q)
    (y : regularSupportedCohomology A m hA i' a q) : Prop :=
  (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp y (zero_add q) =
    (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
      (Ext.mk₀ (t.c v hX hX' a).hom) (add_zero q)

/-- Pullback of a supported Ext class, including its actual closed constant exchange.
Source: ILO XVI 2.2.3.1 (blueprint: def-per-regular-supported-class-operations). -/
abbrev RegularClassPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A m hA)
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : IsPullback w i' i v)
    (hX : IsUnit (m : Γ(X, ⊤))) (hX' : IsUnit (m : Γ(X', ⊤))) (c : ℕ)
    (gamma : RegularSupportedClass A m hA i c)
    (gamma' : RegularSupportedClass A m hA i' c) : Prop :=
  RegularSupportedRestriction A m hA t i i' v w sq hX hX' c (2 * c) gamma gamma'

end AlgebraicGeometry.Etale
