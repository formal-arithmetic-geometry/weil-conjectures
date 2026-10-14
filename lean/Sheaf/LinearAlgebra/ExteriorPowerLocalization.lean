/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Localization of exterior powers

Source: the localization argument of
`new-q1-exterior-sheaf-affine-unit-bijective`, step 2, using the alternating
universal property of exterior powers (Stacks Project, Algebra, Section 00DM).
(blueprint: new-v2-exterior-power-localization). -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace exteriorPower

/-- A map of exterior powers characterized on pure wedges preserves localization.
Source: Stacks Project, Algebra, Section 00DM; the fraction construction in step 2
of `new-q1-exterior-sheaf-affine-unit-bijective`.
(blueprint: new-v2-exterior-power-localization).

Proof: Write N as S⁻¹M via f. The alternating map on fractions sends
(m₁/s₁, ..., mₙ/sₙ) to (m₁ wedge ... wedge mₙ)/(s₁ ... sₙ) in
S⁻¹(⋀^n_R M). This is well defined: replacing a representative multiplies the
numerator equality by an element of S; after multiplication by the product of
all denominators the two wedges agree by multilinearity. The same argument
proves additivity and scalar linearity in each variable and alternation. It is
B-multilinear, since B = S⁻¹R, so the exterior universal property gives a map
from ⋀^n_B N to S⁻¹(⋀^n_R M). Conversely, g extends uniquely to this localization
because every element of S acts invertibly on the B-module ⋀^n_B N. The composites
fix pure wedges of numerators. They fix arbitrary fractions by linearity and
invertibility of denominators, and then all elements since pure wedges span.
Thus g identifies its codomain with the localization of its domain. For n=0,
the construction is the ring localization R → B, with empty denominator product
1. If S contains zero, B and N and both localized exterior powers are zero; the
same formulas still apply. No freeness or finite-generation hypothesis is used. -/
theorem isLocalizedModule_of_wedge
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj N)
    [IsLocalizedModule S f.hom] (n : ℕ)
    (g : ModuleCat.of R (⋀[R]^n M) ⟶
      (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (⋀[B]^n N)))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti B n (fun i ↦ f (a i))) :
    IsLocalizedModule S g.hom := by sorry

end exteriorPower
