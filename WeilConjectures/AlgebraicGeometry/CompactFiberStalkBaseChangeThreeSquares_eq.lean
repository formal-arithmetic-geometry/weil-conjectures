/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChangeData

/-!
# Coherence obligation for compact-support stalk base change
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Three-square compatibility after a further base change. Source: latest
blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(parent: lem-pur-cfiber-stalk-base-change). The three exchange components
are written separately, and both inverse-image compositors and the final
compactification transport are retained.
(blueprint: lem-pur-cfiber-stalk-base-change-three-squares-coherence)

Proof. Apply the two-square pasting of
`compactFiberStalkBaseChangeSquare_eq` (for arbitrary pullback squares, before
taking sections) first to `sq₁, sq₂` and then to the pasted square with `sq₃`
(thm-cbc-finite-torsion, pasting clause). The two inverse-image compositors are
combined by the associativity of `leftDerivedUpperStarComp`
(lem-weil-pbc-inverse-image-composition), which is the isomorphism `e` of the
statement, and the two compactification comparisons are combined by the cocycle
property of `rightDerivedLowerShriekOfCompactificationIso` (both are the
comparisons through common refinements of compactifications of `f₃`). Applying
`RΓ(T, -)` gives the equation. -/
theorem compactFiberStalkBaseChangeThreeSquares_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X₁ X₂ X₃ Y Y₁ Y₂ T : Scheme.{u}}
    {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f₃ : X₃ ⟶ T}
    {g₁ : Y₁ ⟶ Y} {g₂ : Y₂ ⟶ Y₁} {b : T ⟶ Y₂}
    {a₁ : X₁ ⟶ X} {a₂ : X₂ ⟶ X₁} {a₃ : X₃ ⟶ X₂}
    [QuasiCompact f₃]
    (sq₁ : IsPullback a₁ f₁ f g₁) (sq₂ : IsPullback a₂ f₂ f₁ g₂)
    (sq₃ : IsPullback a₃ f₃ f₂ b) (c : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    compactFiberStalkBaseChangeThreeSquares A sq₁ sq₂ sq₃ c K := by
  -- The combined mate/coherence calculation is a separate proof obligation.
  sorry

end WeilConjectures
