/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage


public import Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionAtlas

/-! # PolynomialDualityAffineRealization

Source: Stacks duality.tex, 0E2X and 0BV2; dualizing.tex, 0BZI and 0BZJ.
(blueprint: def-trf-polynomial-duality-affine-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- Exactness proof data for the affine realization, without any chosen mathematical data.
Source: Stacks 01HV, 06Z0 (blueprint: def-trf-polynomial-duality-affine-realization). -/
class PolynomialAffineExactData {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (E : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace)) where
  [additive : E.Additive]
  [limits : PreservesFiniteLimits E]
  [colimits : PreservesFiniteColimits E]

attribute [instance] PolynomialAffineExactData.additive
  PolynomialAffineExactData.limits PolynomialAffineExactData.colimits

/-- Exact module-to-scheme realization with the prescribed localization universes.
Source: Stacks 06Z0 (blueprint: def-trf-polynomial-duality-affine-realization). -/
def polynomialExactRealization
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {A : Type u} [CommRing A] (Y : Scheme.{u})
    (E : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [d : PolynomialAffineExactData E] :
    DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedCategory Y :=
  E.mapDerivedCategory.{u, w}

/-- The actual exact derived associated-sheaf functor, with no choice of equivalence.
Source: Stacks 06Z0 (blueprint: def-trf-polynomial-duality-affine-realization). -/
def polynomialAffineTilde
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedCategory (Spec (.of A)) := by
  letI : HasDerivedCategory.{w} (Spec (.of A)).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)))
  exact (tilde.functor (.of A)).mapDerivedCategory

/-- Exact restriction followed by tilde, with both module localizations in universe u.
Source: Stacks 06Z0 (blueprint: def-trf-polynomial-duality-affine-realization). -/
def polynomialRestrictionTildeComposition
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {B A : Type u} [CommRing B] [CommRing A] (p : B →+* A)
    [_dAmbient : PolynomialAffineExactData (tilde.functor (.of B))]
    [_d : PolynomialAffineExactData (ModuleCat.restrictScalars p ⋙ tilde.functor (.of B))] :
    polynomialExactRealization (Spec (.of B))
        (ModuleCat.restrictScalars p ⋙ tilde.functor (.of B)) ≅
      (ModuleCat.restrictScalars p).mapDerivedCategory.{u, u} ⋙ polynomialAffineTilde B := by
  letI : HasDerivedCategory.{w} (Spec (.of B)).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of B)).toRingedSpace)))
  exact Functor.mapDerivedCategoryCompIso _ _

/-- An ordinary affine direct-image comparison is fixed by the tilde/Gamma unit.
In particular it cannot be multiplied by a unit of the coefficient ring.
Source: Stacks 01I7, 01I9 (blueprint: def-trf-polynomial-duality-affine-realization). -/
def IsPolynomialTildePushforward {P A : Type u} [CommRing P] [CommRing A]
    (p : P →+* A)
    (σ : ModuleCat.restrictScalars p ⋙ tilde.functor (.of P) ≅
      tilde.functor (.of A) ⋙ Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom p))) : Prop :=
  ∀ M : ModuleCat.{u} A,
    (tilde.adjunction (R := .of P)).homEquiv _ _ (σ.hom.app M) =
      (ModuleCat.restrictScalars p).map ((tilde.adjunction (R := .of A)).unit.app M) ≫
        (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom p)).inv.app
          ((tilde.functor (.of A)).obj M)

/-- Localization on the shared scheme-module category, with its chosen Hom universe.
Source: Stacks 05RU (blueprint: def-trf-polynomial-duality-affine-realization). -/
def polynomialSchemeQh
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    (Z : Scheme.{u}) :
    HomotopyCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ) ⥤
      schemeDerivedCategory Z :=
  DerivedCategory.Qh

/-- The comparison from an exact complex model to its actual derived direct image.
It uses the original right-derived unit, so it fixes representative normalizations.
Source: Stacks 079V (blueprint: def-trf-polynomial-duality-affine-realization). -/
@[irreducible] def polynomialExactImageUnit
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {A : Type u} [CommRing A] {Y Z : Scheme.{u}}
    (E : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [d : PolynomialAffineExactData E] (g : Y ⟶ Z)
    [imageAdditive : (E ⋙ Scheme.Modules.pushforward g).Additive]
    (I : HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) :
    (polynomialSchemeQh Z).obj
      (((E ⋙ Scheme.Modules.pushforward g).mapHomotopyCategory (.up ℤ)).obj I) ⟶
      (RingedSpace.derivedModuleDirectImage g.toLRSHom.toShHom).obj
        (E.mapDerivedCategory.{u, w}.obj (DerivedCategory.Qh.obj I)) := by
  letI : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  letI : HasDerivedCategory.{w} Z.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
  exact (Scheme.Modules.pushforward g).rightDerivedFunctorUnit.app
      ((E.mapHomotopyCategory (.up ℤ)).obj I) ≫
    (RingedSpace.derivedModuleDirectImage g.toLRSHom.toShHom).map
      (E.mapDerivedCategoryFactorsh.inv.app I)

/-- A derived affine comparison must be the localization of its specified ordinary map,
using the original direct-image units on every complex, not just a bare isomorphism.
Source: Stacks 06Z0, 079V (blueprint: def-trf-polynomial-duality-affine-realization). -/
def IsPolynomialDerivedImageComparison
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {A : Type u} [CommRing A] {Y Y' Z : Scheme.{u}}
    (E : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [d : PolynomialAffineExactData E]
    (E' : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings Y'.toRingedSpace))
    [d' : PolynomialAffineExactData E']
    (g : Y ⟶ Z) (g' : Y' ⟶ Z)
    [imageAdditive : (E ⋙ Scheme.Modules.pushforward g).Additive]
    [imageAdditive' : (E' ⋙ Scheme.Modules.pushforward g').Additive]
    (σ : E ⋙ Scheme.Modules.pushforward g ≅ E' ⋙ Scheme.Modules.pushforward g')
    (τ : E.mapDerivedCategory.{u, w} ⋙
        RingedSpace.derivedModuleDirectImage g.toLRSHom.toShHom ≅
      E'.mapDerivedCategory.{u, w} ⋙
        RingedSpace.derivedModuleDirectImage g'.toLRSHom.toShHom) : Prop :=
  ∀ I : HomotopyCategory (ModuleCat.{u} A) (.up ℤ),
    polynomialExactImageUnit E g I ≫ τ.hom.app (DerivedCategory.Qh.obj I) =
      (polynomialSchemeQh Z).map ((NatTrans.mapHomotopyCategory σ.hom (.up ℤ)).app I) ≫
        polynomialExactImageUnit E' g' I

end AlgebraicGeometry
