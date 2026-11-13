/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PicardBaseChangeStalkFiniteBases
import WeilConjectures.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq

/-! # Equal finite ranks of the stalks in Picard base change

## References

* Stacks Project, Tags 0BDP and 01C6.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The two modules in a Picard base-change map have finite, isomorphic stalks.
This compares the objects only; it makes no assertion about the canonical map.
(Stacks, Tags 0BDP, 01C6) -/
theorem picardRankMatch_baseChange_stalk_ranks {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) (t : T') :
    let P := (Modules.tensorPullback h).obj
      ((Modules.pushforward (pullback.snd f g)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    let Q := (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
      ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    Module.Finite (T'.presheaf.stalk t) (Q.presheaf.stalk t) ∧
      Nonempty (P.presheaf.stalk t ≃ₗ[T'.presheaf.stalk t] Q.presheaf.stalk t) := by
  obtain ⟨⟨r, ⟨bP⟩⟩, ⟨s, ⟨bQ⟩⟩⟩ :=
    picardRankMatch_baseChange_stalk_finite_bases f E g hR h F hF t
  have hrs : r = s := by
    have he := picardRankMatch_baseChange_stalk_finrank_eq f E g hR h F hF t
    simpa only [Module.finrank_eq_card_basis bP, Module.finrank_eq_card_basis bQ,
      Fintype.card_fin] using he
  subst s
  exact ⟨Module.Finite.of_basis bQ, ⟨bP.equiv bQ (Equiv.refl _)⟩⟩

end AlgebraicGeometry.Scheme
