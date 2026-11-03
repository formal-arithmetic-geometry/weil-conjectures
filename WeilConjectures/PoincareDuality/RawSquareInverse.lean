/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.ProperProjectionComp
public import WeilConjectures.PoincareDuality.ProjectionFormulaShift
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedIsomorphismSquareExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Split-off native specialization; the upstream derived-category comparison is its source.
(blueprint: lem-pod-condensed-cup-projection-intertwining). -/

@[expose] public noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures

set_option maxHeartbeats 4000000 in
-- Native derived-functor comparisons require extra unification heartbeats.
/-- Inverse horizontal pasting of native pullback squares.

Source: the mixed-support cup naturality step of `sk-thm-frobenius.proof.md`,
paragraph 1, via the native pullback and projection comparisons.
(blueprint: lem-pod-condensed-cup-projection-intertwining-native-square).

Proof:
1. Horizontal pasting gives θjp,L = c_(P L) followed by U(θp,L), then θj,(V L), then Q(c⁻¹_L).
2. In an abstract category the equality determines θjp as the corresponding composite isomorphism.
Invert that equality and cancel the boundary c. Functoriality of inversion gives the stated
equation.
3. Perform this cancellation with functors and natural isomorphisms as parameters; specialize the
resulting identity to the native comparisons.
-/
theorem RawSquareInverse
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (p : Z ⟶ Y)
    (x : X ⟶ X) (z : Z ⟶ Z) (y : Y ⟶ Y)
    (sj : CommSq x j j z) (sp : CommSq z p p y)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ.X Y))) :
    ((upperStar Λ.X x).leftDerivedFunctor).map
        ((CondensedRing.leftDerivedUpperStarComp Λ.X j p).inv.app L) ≫
      (pullbackSquareComparison Λ.X (sj.vert_comp sp)).inv.app L =
    (pullbackSquareComparison Λ.X sj).inv.app
        (((upperStar Λ.X p).leftDerivedFunctor).obj L) ≫
      ((upperStar Λ.X j).leftDerivedFunctor).map
        ((pullbackSquareComparison Λ.X sp).inv.app L) ≫
      (CondensedRing.leftDerivedUpperStarComp Λ.X j p).inv.app
        (((upperStar Λ.X y).leftDerivedFunctor).obj L) := by
  sorry

end WeilConjectures
