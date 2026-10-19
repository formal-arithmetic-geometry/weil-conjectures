/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived coefficient change of supported Kummer classes

Source: Stacks Project, Tag 07A6; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md, final paragraph
(blueprint: def-asd-ordinary-supported-kummer-scalar).

## Main definitions

* `SupportedDerivedScalarUnit`: the derived scalar-unit universal property.
* `SupportedKummerScalar`: the normalized scalar-extension square for the classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The normalized degree-zero map associated with an ordinary coefficient unit.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
def exactDerivedScalarUnitMap
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {F : C} {G : B} (η : F ⟶ V.obj G) :
    (DerivedCategory.singleFunctor C 0).obj F ⟶
      V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor B 0).obj G) :=
  (DerivedCategory.singleFunctor C 0).map η ≫
    (V.mapDerivedCategorySingleFunctor 0).inv.app G

/-- The degree-zero scalar-unit property for an exact functor between abelian categories.
This keeps the chosen derived-category structures abstract during construction.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
structure ExactDerivedScalarUnit
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : C) (G : B) (η : F ⟶ V.obj G) : Prop where
  /-- The derived unit represents maps to every restricted derived object. -/
  bijective (K : DerivedCategory B) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor B 0).obj G ⟶ K ↦
      exactDerivedScalarUnitMap V η ≫ V.mapDerivedCategory.map f)

/-- The universal-property formulation of a derived scalar-extension unit at F.
The target is G in degree zero, while test objects K range over the entire unbounded
derived category. This is derived tensor extension, with no flatness assumption on S.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
abbrev SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  ExactDerivedScalarUnit (Sheaf.restrictScalars T.smallEtaleTopology φ) F G η

/-- The scalar-extension clause, with the comparison maps fixed on generators.
Both displayed universal properties refer to the canonical sectionwise scalar maps:
constants send r to φ(r), roots send a ⊗ z to φ(a) ⊗ z. The Ext square is the assertion
that the class itself is obtained by the same derived scalar extension.
Source: Stacks 07A6 and blueprint lem-amb-cartier-kummer-map, final paragraph
(blueprint: def-asd-ordinary-supported-kummer-scalar). -/
@[irreducible]
def SupportedKummerScalar {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (cR : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Scheme.finiteEtaleTateLine T N R hR) 2)
    (cS : Ext ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      (Scheme.finiteEtaleTateLine T N S hS) 2) : Prop :=
  ∃ (η : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (θ : Scheme.finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N S hS)),
    (∀ (U : D.Etaleᵒᵖ) (r : R),
      η.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) ∧
    (∀ (U : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf N).obj.obj U),
      θ.hom.app U (Scheme.finiteEtaleTateOneGenerator R N T hR U r z) =
        Scheme.finiteEtaleTateOneGenerator S N T hS U (φ r) z) ∧
    SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    SupportedDerivedScalarUnit φ T (Scheme.finiteEtaleTateLine T N R hR)
      (Scheme.finiteEtaleTateLine T N S hS) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
      cR.comp (Ext.mk₀ θ) (add_zero 2)


end AlgebraicGeometry.Etale
