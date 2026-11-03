/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
/-!
# The three-factor smooth orientation in relative dimension zero

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
three-factor purity formula and its sum-counit normalization
(blueprint: lem-pur-finite-smooth-gamma-normalization).

The comparison families are quantified with the graph and homotopy normalization equations
of etaleSupportMapCompatibility. That dependency supplies precisely such families. The
right-adjoint coordinates are constructed from the actual adjunctions, not chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

noncomputable section

namespace AlgebraicGeometry.Etale

/-- A finite-type fibre product over a Noetherian scheme is Noetherian. This packages
Mathlib's locally Noetherian and compact-space base-change instances into IsNoetherian.
Source: the item's proof Step 2, finite-type-over-Noetherian permanence
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
instance finiteSmoothPullbackNoetherian {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian (pullback f f) := {}

/-- The type of the compact-support comparison families in etaleSupportMapCompatibility.
This only names its existing quantified family type for use in the coordinate constructions.
Source: Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
abbrev FiniteSmoothCompactSupportComparisons (A : Type (u + 1)) [CommRing A] :=
  ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory

/-- The graph and homotopy normalization equations of etaleSupportMapCompatibility.
The sheaf arrow extends sheet sections by zero off their graphs; its degreewise descent,
followed by the total-derived unit, is the inverse comparison. Thus N is never an
unconstrained isomorphism. Source: Stacks Tags 0F4Y, 0GKM, 0F7L
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothComparisonNormalized (A : Type (u + 1)) [CommRing A]
    (N : FiniteSmoothCompactSupportComparisons A) : Prop :=
  ∃ a : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g,
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
        (a e c).app M ≫ (compactificationSheafToDirectImage A c).app M =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ∧
      (∀ P : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
          (ComplexShape.up ℤ),
        (N e c).inv.app (DerivedCategory.Qh.obj P) =
          compactSupportComparisonOnHomotopy A e c (a e c) P)

/-- Transport the graph-normalized fixed-compactification comparison to R e_!.
Source: Stacks Tags 0F4Y and 0GKM, as normalized by etaleSupportMapCompatibility
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSumComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    N e (HasCompactification.compactification e)

/-- The counit-preserving right-adjoint comparison rho_e, constructed by adjoint uniqueness.
The last transport changes exact degreewise inverse image into its left-derived model.
Source: the item's proof Step 1, Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothAdjointCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedUpperShriek A e ≅
      (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor :=
  (rightDerivedUpperShriekAdjunction A e).rightAdjointUniq
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction).ofNatIsoLeft
      (finiteSmoothSumComparison A N e).symm) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm

/-- Coordinates omega_e ≅ A_V induced by rho_e at A_T.
Source: the item's proof Step 1 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothOmegaCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    dualizingComplex A e ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A V) :=
  (finiteSmoothAdjointCoordinates A N e).app _ ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

/-- Coordinates on the section invariant, obtained by pulling back rho_e at the unit.
Source: the item's proof Steps 1--3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSectionCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] (s : T ⟶ V) :
    sectionInvariant A e s ≅ MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A T) :=
  (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.mapIso
    (finiteSmoothOmegaCoordinates A N e) ≪≫
      leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) s

/-- First factor: pull back the actual exceptional base-change map by the diagonal.
The inverse section compositor identifies Delta^* p_2^* omega_f with omega_f.
Source: three-factor formula, prop-asd-smooth-base-change, proof Step 3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDiagonalFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    dualizingComplex A f ⟶
      sectionInvariant A (pullback.fst f f) (pullback.diagonal f) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.diagonal f)).leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)

/-- Gamma is the canonical smooth tensor map after the inverse three-factor orientation.
Source: sk-thm-smooth-purity, displayed gamma formula
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothGammaMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (α : dualizingComplex A f ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X))
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K ⟶
      (rightDerivedUpperShriek A f).obj K :=
  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).map α.inv ≫
    smoothTensorDualityMap A f
      (isIso_projectionMap_of_finite A f) K

end AlgebraicGeometry.Etale
