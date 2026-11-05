/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
/-! # Divisibility of the kernel of a finite coefficient projection

Source: blueprint main-20261015, coefficient convention in sk-def-sp-coefficient-towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w v z
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
@[irreducible] private def qm {A : Type u} [CommRing A] (π : A) (m r : ℕ) :
    A ⧸ Ideal.span ({π} : Set A) ^ r → A ⧸ Ideal.span ({π} : Set A) ^ (m + r) :=
  Quotient.lift (fun a ↦ Ideal.Quotient.mk _ (π ^ m * a)) (by
    intro a b hab
    apply Ideal.Quotient.eq.mpr
    have h : a - b ∈ Ideal.span ({π} : Set A) ^ r := Ideal.Quotient.eq.mp
      (Quotient.sound hab : Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b)
    rw [← mul_sub]
    have := Ideal.mul_mem_mul (Ideal.pow_mem_pow
      (Ideal.subset_span (Set.mem_singleton π)) m) h
    simpa only [← pow_add, Nat.add_comm m r] using this)

section
variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{u}] [HasSheafify J (Type u)]
  [J.PreservesSheafification (forget CommRingCat.{u})]
  [J.HasSheafCompose (forget CommRingCat.{u})]

end

open WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

end AlgebraicGeometry.ProEtale
