/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.RationalStratumPullbackData


/-! # The ordinary balanced finite-free pullback formula -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RationalStratumPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary finite-free comparison and its two section formulas.
Source: Stacks 06YY and Modules on Sites 03EK; Bhatt--Scholze Remark 6.8.15
(blueprint: lem-per-rational-balanced-free-pullback).

Proof: inverse image carries the free basis to the same free basis, by the free
module adjunction and the actual inverse-image unit. Extension of scalars carries
that basis to the free basis over the target ring. Compose these ordinary
isomorphisms. On pure tensors the forward map sends a tensor (b_j) to the finite
sum of a times the scalar image of b_j times the jth basis vector. This is balanced
by multiplicativity of the structural ring map. The inverse sends a times the jth
basis vector to a times the actual module unit on that vector. One composite fixes
every basis vector. For the other, expand a pure tensor by the finite basis and
move each source coefficient across the tensor using balancing. The formulas commute
with restrictions because the coefficient map and module unit are natural. If the
rank is zero both sums are empty and the same argument gives the zero isomorphism.
This assertion concerns ordinary modules only and has no derived computation clause. -/
theorem rational_balanced_free_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (r : ℕ) :
    ∃ ordinary : (ContinuousRational.modulePull f (coefficient l E f)).obj (free l E X r) ≅
    free l E Y r,
      (∀ (V : X.ProEt)
      (a : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V)))
      (b : Fin r → (rationalCoefficientSheaf l X E).obj.obj (op V)),
    ordinary.hom.val.app (op ((proEtaleBaseChange f).obj V))
        (a • ContinuousRational.moduleUnit f (coefficient l E f) (free l E X r) V
          (∑ j : Fin r, b j • basis l E X r j V)) =
      ∑ j : Fin r,
        (a * scalarImage l E f V (b j)) •
            basis l E Y r j ((proEtaleBaseChange f).obj V)) ∧
      (∀ (V : X.ProEt) (j : Fin r)
      (a : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V))),
    ordinary.inv.val.app (op ((proEtaleBaseChange f).obj V))
        (a • basis l E Y r j ((proEtaleBaseChange f).obj V)) =
      a • ContinuousRational.moduleUnit f (coefficient l E f) (free l E X r) V
        (basis l E X r j V)) := by sorry

end AlgebraicGeometry.Scheme.RationalStratumPullback
