module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Ogoma's lemma
Source: literature/stacks-project/smoothing.tex, Smoothing Ring Maps, Lemma Tag 07FC
(blueprint: lem-weil-pbc-ogoma)
-/

@[expose] public section

universe u v

open scoped Pointwise

/-- Ogoma's lemma, following Stacks Project, Smoothing Ring Maps, Lemma Tag 07FC
(blueprint: lem-weil-pbc-ogoma). The proof follows the five steps in the node:
form the quotient of the two kernel submodules, show its localization vanishes,
use finite generation over a Noetherian ring to obtain a uniform annihilator, and
then verify the kernel equality for every positive power. -/
theorem ogoma_lemma
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Submonoid A) (π : A)
    (h : {x : LocalizedModule S M | π • x = 0} =
      {x : LocalizedModule S M | π • (π • x) = 0}) :
    ∃ s : S, ∀ n : ℕ, 0 < n →
      {m : M | ((s : A)^n * π) • m = 0} =
        {m : M | (((s : A)^n * π)^2) • m = 0} := by
  sorry
