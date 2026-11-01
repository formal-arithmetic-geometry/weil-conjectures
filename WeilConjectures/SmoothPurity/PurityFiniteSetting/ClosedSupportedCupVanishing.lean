/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ClosedUnitIso
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PullbackZero
import WeilConjectures.SmoothPurity.PurityFiniteSetting.TensorPullback

/-!
# Vanishing of the closed-support cup action

Source: Stacks Project, Cohomology, Tags 0G75 to 0G77, and the finite-coefficient
pro-etale tensor-morphism construction (blueprint: lem-pur-closed-supported-cup-vanishing).
The three helper definitions only specialize the published supported cup to full support
and transport its intersection support along the canonical identity-pullback isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The forgetting-support square identifies the ordinary cup with the
forgetful image of the supported cup. Source: Stacks 0G77
(blueprint: lem-pur-closed-ordinary-cup-zero). The proof is the forgetting-support
coefficient restriction square of Tag 0G77, followed by naturality of the
single-tensor comparison and bifunctoriality of tensor. The full-support unitor
and the second-projection support map identify the resulting two composites.
The checked FunctorialCupAlgebraLaws has no cup-forgetting field; its pullback
field and the localization forget_support field do not directly prove this square. -/
theorem closedOrdinaryCupForget_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a b : ℕ) (t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X (a : ℤ) t)
    (β : P.FunctorialCupH true i (b : ℤ) s) :
    P.closedOrdinaryCup X a b t s α (P.functorialCupForget true i b s β) =
      P.functorialCupForget true i (a + b) (t + s)
        (P.closedSupportedCup i a b t s α β) := by
  sorry

end WeilConjectures.PurityFiniteSetting
