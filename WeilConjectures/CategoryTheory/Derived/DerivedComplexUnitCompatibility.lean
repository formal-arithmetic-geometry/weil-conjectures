/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Compatibility laws for the right-derived unit on complexes

The laws are proved directly from the quotient comparison isomorphisms.
Source: Stacks Tags 070I and 015F
(blueprint: lem-cbc-derived-complex-unit-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w₁ w₂ v₁ v₂ u₁ u₂
namespace CategoryTheory
open Abelian Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]

/-- The right-derived unit transferred from homotopy complexes to complexes by the
canonical quotient comparison. This is an explicit composite, with no chosen data.
Source: Stacks Tag 015F (blueprint: lem-cbc-derived-complex-unit-compatibility). -/
@[no_expose] def derivedComplexUnit (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app J)

end CategoryTheory
