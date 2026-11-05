/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimensions of quotients of finitely generated algebras over a field

- `PrimeSpectrum.topologicalKrullDim_closure_singleton`: the closure of a point `𝔭` of
  `Spec R` has the dimension of `R ⧸ 𝔭`.
- `ringKrullDim_quotient_comap_le`: for a map `φ : A → B` of finitely generated algebras over a
  field and a prime `𝔓` of `B`, `dim A ⧸ φ⁻¹(𝔓) ≤ dim B ⧸ 𝔓`, both dimensions being transcendence
  degrees.
-/

@[expose] public section

/-- A nontrivial finitely generated algebra over a field has finite Krull dimension. -/
lemma exists_ringKrullDim_eq_natCast_of_finiteType (k R : Type*) [Field k] [CommRing R]
    [Nontrivial R] [Algebra k R] [Algebra.FiniteType k R] : ∃ n : ℕ, ringKrullDim R = n := by
  have h1 := ringKrullDim_ne_top_of_finiteType k R
  have h2 : ringKrullDim R ≠ ⊥ :=
    ne_bot_of_le_ne_bot WithBot.coe_ne_bot ringKrullDim_nonneg_of_nontrivial
  induction h : ringKrullDim R using WithBot.recBotCoe with
  | bot => exact absurd h h2
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd h h1
    | coe m => exact ⟨m, rfl⟩

