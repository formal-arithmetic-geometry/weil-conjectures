/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SingleProperOpenArrows

/-!
# Evaluation of the intrinsic inverse-image/open-extension comparison

Source: Stacks Project, Tags 09AE and 0F7B, exact derived localization.
(blueprint: lem-cbc-strict-tower-alpha-single-evaluation)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

/-- Evaluation carries the intrinsic clopen alpha to its single-level exact localization.
Source: Stacks Tags 09AE and 0F7B, exact derived localization
(blueprint: lem-cbc-strict-tower-alpha-single-evaluation).
Proof: before localization, evaluate the termwise open extension and inverse image.
Their comparisons are the identity on the evaluated module sheaves. Their adjunction
units and counits are termwise, so the open-unit transpose defining beta evaluates
to `singleBetaInv`; its canonical inverse evaluates to the inverse used in
`singleAlpha`. For the clopen lift, the ordinary open-to-direct-image map is the
unit followed by direct image of the inverse open unit. This formula is termwise.
Direct image along a clopen immersion is exact. Its normalized derived adjunction
therefore identifies the derived projector with the localization of `singlePi`.
The open and inverse-image compositors are the unit-normalized ones, so they too
evaluate to their single-level compositors. Substitute these four component
identities in the projected-comparison formula. Exact localization preserves their
composition and gives the displayed square on Qh of every complex. Naturality and
essential surjectivity of Qh extend the square to every derived tower. No
faithfulness of evaluation on derived morphisms is used. -/
theorem alpha_single_evaluation (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (N : Derived B S) (n : ℕ) :
    (ev B W n).map ((alpha B k r p i h).app N) ≫
        (evalJ B k n).hom.app ((G B r).obj N) ≫
        (moduleJ B k).mapDerivedCategory.map ((evalG B r n).hom.app N) =
      (evalG B p n).hom.app ((J B i).obj N) ≫
        (modulePullback B p).mapDerivedCategory.map ((evalJ B i n).hom.app N) ≫
        (singleDerivedAlpha B k r p i h).app ((ev B S n).obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower
