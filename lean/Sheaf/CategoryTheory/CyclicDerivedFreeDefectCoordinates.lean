/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.CategoryTheory.CyclicDerivedFreeHomCoordinates

/-! # The free cyclic differential in adjunction coordinates

Source: Stacks Tags 0149, 0152, and the normalized cyclic free resolution.
(blueprint: lem-sf-cyclic-free-defect-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- Evaluation of the cyclic difference on a free adjunct gives 1 minus the inverse
cyclic action. Equivalently, evaluating it on T(u) gives -(1-T)(u). This is a
calculation of the differential, with no assertion about exactness or a boundary.

Proof: first work on chain representatives. An adjunct of u has summand n equal
to theta_N,n composed with the n-th translate of u. Precomposing by d and evaluating
on summand zero gives u minus its summand -1, namely (1-T⁻¹)u, by the prescribed
summand formula for d. Applying this to T(u) gives T(u)-u. Localize the calculation
using differential_fac and the standard exact-functor factorization isomorphisms.
Naturality allows replacement of representatives by their localization isomorphisms.
For the second equation move the source shift to the target using shiftEquiv and
apply the same calculation with target N[-1]; the shift comparison is precisely
the one in cyclicDerivedHomAction. There is no rotation sign in precomposition
by d[1], so the result is again T(u)-u. No boundedness is used.
Source: parent calculus step 2, free-resolution summand calculation, Stacks 0149, 0152
(blueprint: lem-sf-cyclic-free-defect-coordinates). -/
theorem cyclicDerivedFreeDefect_coordinates (R : CyclicDerivedFreeResolution F)
    (M N : DerivedCategory (IsoAlgebra F)) :
    (∀ u : CyclicDerivedHom F M N 0,
      cyclicDerivedFreeHomEquiv F M N
        (R.differential.app M ≫ (cyclicDerivedFreeHomEquiv F M N).symm
          (cyclicDerivedHomAction F M N 0 u)) = -cyclicDerivedHomDefect F M N 0 u) ∧
    (∀ u : CyclicDerivedHom F M N (-1),
      cyclicDerivedFreeShiftedHomEquiv F M N
        ((R.differential.app M)⟦(1 : ℤ)⟧' ≫
          (cyclicDerivedFreeShiftedHomEquiv F M N).symm
            (cyclicDerivedHomAction F M N (-1) u)) =
        -cyclicDerivedHomDefect F M N (-1) u) := by sorry

end CategoryTheory.Endofunctor.IsoAlgebra
