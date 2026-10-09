/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Descent of finite presentation and rank of modules along faithfully flat maps

For a faithfully flat `A`-algebra `B` and an `A`-module `M`: if `B ⊗[A] M` is finitely presented
over `B` then so is `M`; and the rank of `M` at a prime is the rank of `B ⊗[A] M` at any prime
over it.

## Main results

- `Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`
- `Module.rankAtStalk_eq_of_rankAtStalk_tensorProduct_eq`
-/

@[expose] public section

open TensorProduct

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- **Finite presentation descends along faithfully flat maps.** -/
lemma Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat A B] [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M := by
  have : Module.Finite A M := .of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, l, hl⟩ := Module.Finite.exists_fin' A M
  rw [← Module.FinitePresentation.fg_ker_iff l hl]
  -- `B ⊗ ker l` is the kernel of the surjection `B ⊗ l`, which is finitely generated
  have hbl : Function.Surjective (AlgebraTensorModule.lTensor B B l) :=
    LinearMap.lTensor_surjective B hl
  have hfg : (LinearMap.ker (AlgebraTensorModule.lTensor B B l)).FG :=
    Module.FinitePresentation.fg_ker _ hbl
  have : Module.Finite B (B ⊗[A] LinearMap.ker l) := by
    have : Module.Finite B (LinearMap.ker (AlgebraTensorModule.lTensor B B l)) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (LinearMap.tensorKerEquiv B B l).symm
  rw [← Module.Finite.iff_fg]
  exact .of_finite_tensorProduct_of_faithfullyFlat B

/-- **Rank descends along faithfully flat maps**: if `B ⊗[A] M` has rank `r` at every prime of
`B`, then `M` has rank `r` at every prime of `A`. -/
lemma Module.rankAtStalk_eq_of_rankAtStalk_tensorProduct_eq [Module.FaithfullyFlat A B]
    [Module.Finite A M] [Module.Flat A M] {r : ℕ}
    (h : ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = r := by
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  rw [← Module.rankAtStalk_baseChange, h]
