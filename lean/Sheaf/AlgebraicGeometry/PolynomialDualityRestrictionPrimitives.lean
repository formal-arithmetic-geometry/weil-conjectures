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


public import Sheaf.AlgebraicGeometry.PolynomialDualityPresentationData

/-! # PolynomialDualityRestrictionPrimitives

Source: Stacks duality.tex, 0E2X and 0BV2; dualizing.tex, 0BZI and 0BZJ.
(blueprint: def-trf-polynomial-duality-restriction-primitives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry

/-- Exact open restriction, with the native sectionwise restriction functor.
Source: Stacks 0E2X (blueprint: def-trf-polynomial-duality-restriction-primitives). -/
def polynomialOpenRestriction
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    schemeDerivedCategory Z ⥤ schemeDerivedCategory Y :=
  by
  letI : HasDerivedCategory.{w} Z.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
  letI : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  exact (Scheme.Modules.restrictFunctor j).mapDerivedCategory

/-- The sectionwise open restriction adjunction with the original derived direct-image unit.
Source: Stacks 0E2X (blueprint: def-trf-polynomial-duality-restriction-primitives). -/
def polynomialOpenAdjunction
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] :
    polynomialOpenRestriction j ⊣ RingedSpace.derivedModuleDirectImage j.toLRSHom.toShHom := by
  letI : HasDerivedCategory.{w} Z.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
  letI : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  exact (Scheme.Modules.restrictAdjunction j).mapDerivedCategoryRightDerivedAdjunction

/-- Composition with the original derived-direct-image units, not a free isomorphism.
Source: Stacks 0D5T (blueprint: def-trf-polynomial-duality-restriction-primitives). -/
@[irreducible] def polynomialImageComposition
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {Y Z W : RingedSpace.{u}} (a : Y ⟶ Z) (b : Z ⟶ W) :
    RingedSpace.derivedModuleDirectImage a ⋙ RingedSpace.derivedModuleDirectImage b ≅
      RingedSpace.derivedModuleDirectImage (a ≫ b) :=
  Classical.choose (RingedSpace.exists_derivedModuleDirectImageComposition a b)

/-- The direct-image square from equality of the two composite ringed-space maps.
Both legs use the original derived-functor units.
Source: Stacks 0D5T, 0E2X (blueprint: def-trf-polynomial-duality-restriction-primitives). -/
@[irreducible] def polynomialImageSquare
    [∀ Z : RingedSpace.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
    {Y Z Z' W : RingedSpace.{u}} (a : Y ⟶ Z) (b : Z ⟶ W)
    (c : Y ⟶ Z') (d : Z' ⟶ W) (h : a ≫ b = c ≫ d) :
    RingedSpace.derivedModuleDirectImage a ⋙ RingedSpace.derivedModuleDirectImage b ≅
      RingedSpace.derivedModuleDirectImage c ⋙ RingedSpace.derivedModuleDirectImage d :=
  polynomialImageComposition a b ≪≫
    eqToIso (congrArg RingedSpace.derivedModuleDirectImage h) ≪≫
      (polynomialImageComposition c d).symm

/-- The categorical exchange map is the mate of the unit of the algebra restriction.
In the application the square is the actual ringed-space direct-image square.
Source: Stacks 08IB, 0E2X (blueprint: def-trf-polynomial-duality-restriction-primitives). -/
@[irreducible] def polynomialRestrictionExchange
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {T : A ⥤ B} {T' : C ⥤ D} {L : B ⥤ D} {R : D ⥤ B}
    {F : A ⥤ C} {G : C ⥤ A} (adj : L ⊣ R) (adjF : F ⊣ G)
    (square : T' ⋙ R ≅ G ⋙ T) (M : A) :
    L.obj (T.obj M) ⟶ T'.obj (F.obj M) :=
  (adj.homEquiv _ _).symm
    (T.map (adjF.unit.app M) ≫ square.inv.app (F.obj M))

/-- The coinduction restriction is the mate of restriction of evaluation at one.
It is independently specified before any global dualizing object or chart identification.
Source: Stacks 0BUZ, 0E2X (blueprint: def-trf-polynomial-duality-restriction-primitives). -/
@[irreducible] def polynomialCoinductionRestriction
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {T : A ⥤ B} {T' : C ⥤ D} {H : B ⥤ A} {H' : D ⥤ C}
    {L : B ⥤ D} {R : D ⥤ B} {F : A ⥤ C} {G : C ⥤ A}
    (adj : L ⊣ R) (adjF : F ⊣ G) (adjH : T ⊣ H) (adjH' : T' ⊣ H')
    (square : T' ⋙ R ≅ G ⋙ T) (N : B)
    [IsIso (polynomialRestrictionExchange adj adjF square (H.obj N))] :
    F.obj (H.obj N) ⟶ H'.obj (L.obj N) :=
  (adjH'.homEquiv _ _)
    (inv (polynomialRestrictionExchange adj adjF square (H.obj N)) ≫
      L.map (adjH.counit.app N))

end AlgebraicGeometry
