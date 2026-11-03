/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange

/-! # Invertibility of the canonical compact-support Frobenius exchange

Source: lem-fix-weil-operations.proof.md, first paragraph, automorphism-square
invertibility. The proof uses the specified proper direct exchange and the specified
inverse open exchange, with no replacement of either comparison.
(blueprint: lem-sf-compact-automorphism-exchange-invertible)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.FrobeniusSquareExchange

/-- The canonical compact-support exchange for automorphisms is invertible on the
whole underlying derived category.

Source: lem-fix-weil-operations.proof.md, paragraph 1, inverse-square argument
(blueprint: lem-sf-compact-automorphism-exchange-invertible).

Proof: the specified proper direct exchange is an isomorphism by
`condensed_isomorphism_square_exchange`. The open exchange in `compact` is the
composite of the exact/left-derived comparison, the inverse of the normalized open
comparison, and the inverse exact/left-derived comparison. All three are
isomorphisms. Whiskering and composition preserve invertibility. This works also
for identity automorphisms and empty schemes, and uses no proper-base-change
or constructibility theorem. -/
theorem compact_isIso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {gX : X ⟶ X} {gbar : c.Z ⟶ c.Z} {gY : Y ⟶ Y}
    [IsIso gX] [IsIso gbar] [IsIso gY]
    (sqP : CommSq gbar c.g c.g gY) (sqJ : CommSq gX c.i c.i gbar) :
    IsIso (compact Λ c sqP sqJ) := by
  let : IsIso (direct Λ c.g (sq := sqP)) :=
    (CondensedRing.condensed_isomorphism_square_exchange Λ sqP).2.2.2.2.2.2
  unfold compact
  dsimp only [id]
  infer_instance


end WeilConjectures.FrobeniusSquareExchange
