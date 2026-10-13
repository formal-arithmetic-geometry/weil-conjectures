/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

/-! # Power torsion of Hom from a bounded finite-projective complex

Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory

/-- Elementwise power torsion of all cohomology modules implies power torsion of
morphisms from a bounded complex of finite projective modules.
Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).

Proof: Induct on the length of a finite interval supporting P, simultaneously for
all targets with the displayed cohomological torsion property. The zero complex
has no nonzero morphisms. For a single projective term in degree t, projectivity
identifies derived Hom with module Hom into H^t(M). Choose a finite generating
set of that term. Each generator's image is killed by a power of r; the maximum
of these finitely many exponents kills the map by linearity. For more than one
term, the highest-degree term and the shorter stupid truncation give a distinguished
triangle. Restrict the given morphism to the highest-degree single term and kill it
by r^a using the single-term case. Exactness of contravariant Hom into M lifts
r^a times the morphism to the shorter truncation. Induction kills the lift by r^b.
Linearity of composition and r^(a+b) = r^b * r^a then kill the original morphism.
The argument uses no boundedness or finiteness hypothesis on M. Empty generating
sets, the zero ring and the zero complex all give zero Hom and exponent zero. -/
theorem bounded_projective_hom_power_torsion
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (r : A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hb : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (hf : ∀ i : ℤ, Module.Finite A (P.X i))
    (hp : ∀ i : ℤ, Module.Projective A (P.X i))
    (M : DerivedCategory (ModuleCat.{u} A))
    (hM : ∀ (i : ℤ) (m : (homologyFunctor (ModuleCat.{u} A) i).obj M),
      ∃ n : ℕ, r ^ n • m = 0)
    (α : Q.obj P ⟶ M) :
    ∃ n : ℕ, r ^ n • α = 0 := by sorry

end DerivedCategory
