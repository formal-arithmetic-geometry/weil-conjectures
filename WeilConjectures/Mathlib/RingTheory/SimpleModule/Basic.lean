/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Induction on finite modules over a finite ring

Every nonzero finite module `M` over a finite commutative ring `R` has a simple submodule `N`,
which is isomorphic to `R ⧸ 𝔪` for a maximal ideal `𝔪`, and the quotient `M ⧸ N` has fewer
elements than `M`. Hence a property of `R`-modules which is invariant under isomorphism, holds
for the zero modules and for the residue fields `R ⧸ 𝔪`, and is stable under extensions, holds
for every finite `R`-module.

## Main results

- `ModuleCat.induction_on_finite`: the induction principle above.
-/

@[expose] public section

universe v

open CategoryTheory

namespace ModuleCat

variable {R : Type v} [CommRing R] [Finite R]

/-- **Dévissage of finite modules over a finite ring.** A property `P` of `R`-modules, for a
finite commutative ring `R`, which is invariant under isomorphism, holds for the zero modules and
for the residue fields `R ⧸ 𝔪` at the maximal ideals `𝔪`, and which holds for the middle term of
a short exact sequence as soon as it holds for its outer terms, holds for every finite
`R`-module. -/
theorem induction_on_finite (P : ModuleCat.{v} R → Prop)
    (iso : ∀ {M N : ModuleCat.{v} R}, (M ≅ N) → P M → P N)
    (zero : ∀ M : ModuleCat.{v} R, Subsingleton M → P M)
    (simple : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → P (ModuleCat.of R (R ⧸ 𝔪)))
    (extension : ∀ S : ShortComplex (ModuleCat.{v} R), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (M : ModuleCat.{v} R) [Module.Finite R M] : P M := by
  induction hn : Nat.card M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  rcases subsingleton_or_nontrivial M with hM₀ | hM₀
  · exact zero M hM₀
  obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
  obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (isSimpleModule_iff_isAtom.mpr hN)
  refine extension _ (LinearMap.shortExact_shortComplexKer N.mkQ_surjective)
    (iso (LinearEquiv.toModuleIso (e.symm.trans (LinearEquiv.ofEq _ _ N.ker_mkQ.symm)))
      (simple 𝔪 h𝔪)) (ih _ ?_ (ModuleCat.of R (M ⧸ N)) rfl)
  have : Finite M := Module.finite_of_finite R
  have : Finite (M ⧸ N) := Module.finite_of_finite R
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN.1
  have : 1 < Nat.card N := Finite.one_lt_card
  have : 0 < Nat.card (M ⧸ N) := Nat.card_pos
  have := N.card_eq_card_quotient_mul_card
  rw [← hn]
  dsimp only [ModuleCat.of]
  nlinarith

end ModuleCat
