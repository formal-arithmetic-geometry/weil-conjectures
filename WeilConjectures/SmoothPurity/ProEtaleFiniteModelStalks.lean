/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Finite geometric stalks of finite local models -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

private noncomputable def geometricFiber {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) : X.ProEt ⥤ Type (u + 1) where
  obj U := ULift.{u + 1} ((Over.mk x) ⟶ (ProEt.forget X).obj U)
  map f := ↾fun y ↦ ⟨y.down ≫ (ProEt.forget X).map f⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.ProEtale
