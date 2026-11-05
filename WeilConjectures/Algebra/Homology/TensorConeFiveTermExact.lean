/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated

/-! # Exact cohomology of the extended and tensored cone triangle

Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-tensor-cone-five-term-exact).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable {A C : Type u} [CommRing A] [CommRing C]
  (ρ : A →+* C) {P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ}
  (f : P₁ ⟶ P₂) (N : CochainComplex (ModuleCat.{u} C) ℤ)

end ModuleCat
