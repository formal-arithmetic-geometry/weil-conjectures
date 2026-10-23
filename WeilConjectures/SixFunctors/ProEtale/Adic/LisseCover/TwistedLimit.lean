/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Twisted sections over inverse limits

Let `f : V ⟶ Y` be quasi-compact and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). For a cofiltered system `(Dⱼ)` of quasi-compact
quasi-separated `Y`-schemes with affine transition maps and limit `D`, every twisted section of
`c` over `D` comes from a twisted section over some `Dⱼ`
(`AlgebraicGeometry.IsTwistedSection.exists_of_isLimit`): a locally constant function on the
quasi-compact `V ×_Y D = lim V ×_Y Dⱼ` is given by finitely many quasi-compact open and closed
subsets, which come from a finite stage, and the compatibility with `c`, an equality of two
locally constant functions on `(V ×_Y D) ×_D (V ×_Y D)`, holds at a finite stage, a closed
subset with empty preimage in the limit being empty at a finite stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} {f : V ⟶ Y}

/-- **Twisted sections over a limit come from a finite stage.** -/
theorem IsTwistedSection.exists_of_isLimit [QuasiCompact f] {S : Type*}
    {c : ↥(pullback f f) → S → S} {J : Type u} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ Scheme.{u}} [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    {C : Cone D} (hC : IsLimit C) (π : ∀ j, D.obj j ⟶ Y)
    (hπ : ∀ {i j} (g : i ⟶ j), D.map g ≫ π j = π i) (π' : C.pt ⟶ Y)
    (hπ' : ∀ j, C.π.app j ≫ π j = π') {σ : ↥(pullback f π') → S}
    (hσ : IsTwistedSection f c π' σ) :
    ∃ (j : J) (σⱼ : ↥(pullback f (π j)) → S), IsTwistedSection f c (π j) σⱼ ∧
      σⱼ ∘ (pullbackMapRight f (C.π.app j) (hπ' j)).base = σ :=
  sorry

end AlgebraicGeometry
