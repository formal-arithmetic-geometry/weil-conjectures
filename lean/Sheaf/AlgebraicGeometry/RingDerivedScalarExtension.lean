/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

/-! # Derived scalar extension for ordinary modules

Source: Stacks Project Tags 06YY and 07A6 (blueprint: def-zl-ring-derived-scalar-extension).

This module records the canonical ordinary-module derived restriction and its left
adjoint used by the condensed evaluation statement.  The underlying constructions are
those of the published constant-realization module, with no alternate choice of derived
functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe r wR wS wT

open CategoryTheory

namespace CategoryTheory.RingDerivedScalarExtension

/-- Derived restriction of scalars along a commutative ring homomorphism.

Source: Stacks Project Tag 07A6 (blueprint: def-zl-ring-derived-scalar-extension).
-/
abbrev moduleDerivedRestriction {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    DerivedCategory (ModuleCat.{r} B) ⥤ DerivedCategory (ModuleCat.{r} A) :=
  ConstantScalarRealization.moduleDerivedRestriction.{wR, wS, r} f

/-- The derived restriction functor has the canonical right-adjoint structure.

Source: Stacks Project Tag 07A6 (blueprint: def-zl-ring-derived-scalar-extension).
-/
instance moduleDerivedRestriction_rightAdjoint {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    (moduleDerivedRestriction f).IsRightAdjoint :=
  ConstantScalarRealization.moduleDerivedRestriction_rightAdjoint f

/-- Derived extension of scalars, fixed as the left adjoint of restriction.

Source: Stacks Project Tags 06YY and 07A6
(blueprint: def-zl-ring-derived-scalar-extension).
-/
def moduleDerivedExtension {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    DerivedCategory (ModuleCat.{r} A) ⥤ DerivedCategory (ModuleCat.{r} B) :=
  (moduleDerivedRestriction f).leftAdjoint

/-- Canonical composition of exact derived scalar restrictions, including a specified
identification of the composite ring map. This re-exposes the existing comparison
without depending on the constant-realization theorem's conclusion.
Source: Stacks Project Tag 0D6D (blueprint: def-zl-ring-derived-scalar-extension). -/
def moduleDerivedRestrictionComposition
    {A B D : Type r} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) (h : A →+* D) (hcomp : g.comp f = h)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)]
    [HasDerivedCategory.{wT} (ModuleCat.{r} D)] :
    moduleDerivedRestriction g ⋙ moduleDerivedRestriction f ≅ moduleDerivedRestriction h :=
  ConstantScalarRealization.moduleDerivedRestrictionComposition f g ≪≫
    eqToIso (congrArg (fun a : A →+* D ↦ moduleDerivedRestriction a) hcomp)

/-- The unit-preserving scalar-extension associator, obtained by uniqueness of left
adjoints from the specified exact-restriction composition. The composite ring map
may be supplied with its defining equality, as for the projections of a ring limit.
Source: Stacks Project Tags 06YY, 07A6 and 0D6D
(blueprint: def-zl-ring-derived-scalar-extension). -/
def moduleDerivedExtensionComposition
    {A B D : Type r} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) (h : A →+* D) (hcomp : g.comp f = h)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)]
    [HasDerivedCategory.{wT} (ModuleCat.{r} D)] :
    moduleDerivedExtension f ⋙ moduleDerivedExtension g ≅ moduleDerivedExtension h :=
  (((Adjunction.ofIsRightAdjoint (moduleDerivedRestriction f)).comp
      (Adjunction.ofIsRightAdjoint (moduleDerivedRestriction g))).ofNatIsoRight
        (moduleDerivedRestrictionComposition f g h hcomp)).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (moduleDerivedRestriction h))

end CategoryTheory.RingDerivedScalarExtension
