/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Adjoin.FG

/-!
# The poset of finitely generated subalgebras

The finitely generated `R`-subalgebras of an `R`-algebra `A` form a nonempty directed
poset `{S : Subalgebra R A // S.FG}` whose supremum is all of `A`
(`Subalgebra.iSup_val_fg_eq_top`).

This is the algebra analogue of `Module.fgSystem`, and it is the index poset of the
filtered system exhibiting `A` as the colimit of its finitely generated subalgebras.
-/

@[expose] public section

namespace Subalgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

instance nonempty_fg : Nonempty {S : Subalgebra R A // S.FG} := ⟨⟨⊥, fg_bot⟩⟩

instance isDirectedOrder_fg : IsDirectedOrder {S : Subalgebra R A // S.FG} where
  directed S T :=
    ⟨⟨_, S.2.sup T.2⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

/-- The supremum of the finitely generated `R`-subalgebras of `A` is all of `A`: every
element lies in the subalgebra it generates. -/
lemma iSup_val_fg_eq_top : ⨆ S : {S : Subalgebra R A // S.FG}, S.1 = ⊤ :=
  le_antisymm le_top fun x _ ↦
    le_iSup (fun S : {S : Subalgebra R A // S.FG} ↦ S.1)
      ⟨Algebra.adjoin R {x}, {x}, by simp⟩ (Algebra.self_mem_adjoin_singleton R x)

end Subalgebra
