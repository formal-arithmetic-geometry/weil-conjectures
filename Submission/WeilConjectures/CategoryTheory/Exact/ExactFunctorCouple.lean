/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.HalfPlaneConvergence
import Submission.WeilConjectures.CategoryTheory.ExactCoupleConvergence
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Submission.WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import Submission.WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel
import all Submission.WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Exact functors transport exact couples

Source: Stacks Project, Homology, Section 12.21, Tags 011Q, 011R, 011S, 0AMJ,
and the transport argument of the blueprint (blueprint: lem-sp-exact-functor-couple).
The index `r` denotes the actual page `r + 2`. Object equalities identify the initial
mapped datum; subsequent identifications of subobjects are commuting isomorphisms.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {s : ℕ}

private structure Comparison (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) where
  δ : ∀ p q, Φ.obj (X.D p q) ≅ Y.D p q
  φ : ∀ p q, Φ.obj (X.E p q) ≅ Y.E p q
  ha : ∀ p q, Φ.map (X.alpha p q) ≫ (δ (p - 1) (q + 1)).hom =
    (δ p q).hom ≫ Y.alpha p q
  hf : ∀ p q, Φ.map (X.f p q) ≫ (δ (p + 2) (q - 1)).hom =
    (φ p q).hom ≫ Y.f p q
  hg : ∀ p q, Φ.map (X.g p q) ≫ (φ (p + s) (q - s)).hom =
    (δ p q).hom ≫ Y.g p q

variable {Φ}

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem Comparison.hd {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.d p q) ≫ (e.φ (p + 2 + s) (q - 1 - s)).hom =
      (e.φ p q).hom ≫ Y.d p q := by
  dsimp only [d]
  rw [Φ.map_comp, Category.assoc, e.hg, ← Category.assoc, e.hf, Category.assoc]

/-! Transport of exact couples along an exact additive functor.
Source: Stacks Project, Homology, Section 12.21; blueprint: lem-sp-exact-functor-couple.
The full transport construction is retained as the next proof obligation. -/
end CategoryTheory.BigradedExactCouple
