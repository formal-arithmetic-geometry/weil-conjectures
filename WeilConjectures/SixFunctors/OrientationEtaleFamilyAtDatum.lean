/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OrientationEtaleCoefficientTwists
public import WeilConjectures.SixFunctors.OrientationEtaleFamily
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation

/-!
# The finite-etale orientation family at an actual finite datum

This declaration specializes the complete ordinary-etale family to the finite root line.
Every equation is a field of the same record used by the realization square; in particular,
the component used by that square is the `finite_family_component` field below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The full finite-etale orientation family at a finite coefficient stage.  The
component is the shifted root line from `sfOrientationEtaleLine`; all family laws
are retained in this specialized record and the fixed component is tied to the
same family by `component_spec`.
Source: `def-sf-orientation-etale-family` (blueprint: def-sf-orientation-etale-family).
(blueprint: def-sf-orientation-etale-family-at-datum). -/
structure SfFiniteEtaleOrientationAtDatum
    {A : Type (u + 1)} [CommRing A] [Finite A]
    [AlgebraicGeometry.Etale.HasTateTwist A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) where
  component : ∀ (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    [HasCompactification f],
    sfOrientationEtaleLine A N hA X d ≅
      AlgebraicGeometry.Etale.dualizingComplex A f
  finite_family_component : ∀ {U V : Scheme.{u}} (g : U ⟶ V) (d : ℕ)
    [IsSeparated g] [QuasiCompact g] [SmoothOfRelativeDimension d g]
    [HasCompactification g],
    sfOrientationEtaleLine A N hA U d ≅
      AlgebraicGeometry.Etale.dualizingComplex A g
  component_spec : ∀ (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    [HasCompactification f],
    finite_family_component f d = component d
  /-- Base change on the finite root line, with the normalized compact-support
  transpose from the ordinary-etale family. -/
  baseChange : ∀ {U V U' V' : Scheme.{u}} {g : V' ⟶ V} {f' : U' ⟶ V'}
    {f : U ⟶ V} {g' : U' ⟶ U} (sq : IsPullback g' f' f g) (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension d f]
    [HasCompactification f] [IsSeparated f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f'] [HasCompactification f']
    (hU' : IsUnit (N : Γ(U', ⊤))) (hU : IsUnit (N : Γ(U, ⊤))),
    (finite_family_component f' d).hom =
      (sfOrientationEtaleLinePullback A N hN hA g' hU' hU d).inv ≫
      ((Etale.upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor).map
        (finite_family_component f d).hom ≫ Etale.dualizingComplexBaseChangeMap A sq
  /-- Smooth composition, including the tensor multiplication and exceptional
  adjunction mate prescribed by `def-sf-orientation-etale-family`. -/
  composition : ∀ {U V W : Scheme.{u}} (g : U ⟶ V) (h : V ⟶ W) (d e : ℕ)
    [IsSeparated g] [IsSeparated h] [IsSeparated (g ≫ h)]
    [QuasiCompact g] [QuasiCompact h] [QuasiCompact (g ≫ h)]
    [SmoothOfRelativeDimension d g] [SmoothOfRelativeDimension e h]
    [SmoothOfRelativeDimension (d + e) (g ≫ h)] [HasCompactification g]
    [HasCompactification h] [HasCompactification (g ≫ h)]
    (hU : IsUnit (N : Γ(U, ⊤))) (hV : IsUnit (N : Γ(V, ⊤))),
    (finite_family_component (g ≫ h) (d + e)).hom =
      (sfOrientationEtaleProduct A N hN hA U hU d e).inv ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) U).obj
        (sfOrientationEtaleLine A N hA U d)).map
          (sfOrientationEtaleLinePullback A N hN hA g hU hV e).inv ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) U).map
        (finite_family_component g d).hom).app
          (((Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj
            (sfOrientationEtaleLine A N hA V e)) ≫
      Etale.dualizingComplexTensorMap A g
        (sfOrientationEtaleLine A N hA V e) ≫
      (Etale.rightDerivedUpperShriek A g).map
        (finite_family_component h e).hom ≫
      (PurityFiniteSetting.finiteExceptionalComposition A g h).inv.app
        (@MonoidalCategoryStruct.tensorUnit (Etale.DerivedCategoryModule A W) _
          MonoidalCategory.toMonoidalCategoryStruct)
  /-- The affine-line normalization, including the normalized projective-line trace. -/
  affineLine : ∀ (U V : Scheme.{u}) (g : U ⟶ V)
    [IsSeparated g] [QuasiCompact g] [SmoothOfRelativeDimension 1 g]
    [HasCompactification g] [IsNoetherian V]
    [HasCompactification (AffineSpace PUnit.{u + 1} V ↘ V)]
    (hV : IsUnit (N : Γ(V, ⊤))) (_hU : IsUnit (N : Γ(U, ⊤))),
    U = AffineSpace PUnit.{u + 1} V →
    HEq g (AffineSpace PUnit.{u + 1} V ↘ V) →
    HEq ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      (finite_family_component g 1).hom ≫
        (Etale.rightDerivedUpperShriekAdjunction A g).counit.app
          (@MonoidalCategoryStruct.tensorUnit (Etale.DerivedCategoryModule A V) _
            MonoidalCategory.toMonoidalCategoryStruct))
      (sfOrientationAffineTrace A N hN hA V hV)

end WeilConjectures
