/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# Tor amplitude in a monoidal derived category

Let `C` be an abelian category whose derived category `D(C)` carries a monoidal structure, for
instance the derived tensor product `- ⊗ᴸ -` of a category of sheaves. This file defines Tor
amplitude for objects of `D(C)`, tested by tensoring with objects of `C` placed in degree `0`.

Nothing here depends on a site: the étale and pro-étale Tor amplitude of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude` and
`WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude` are specialisations.

## Main definitions

- `DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`.
- `DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.

## Main results

- `DerivedCategory.exists_inf_homologyConcentratedIn_inf_torAmplitudeIn_iff`: for a property
  `P` of bounded objects, an object satisfies `P` and has finite Tor amplitude exactly when,
  for some interval `[a, b]`, it satisfies `P`, has homology concentrated in `[a, b]` and has
  Tor amplitude in `[a, b]`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace DerivedCategory

variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
  [MonoidalCategory (DerivedCategory C)]

/-- An object `M` of `D(C)` has *Tor amplitude in `[a, b]`* if for every object `F` of `C` the
tensor product `M ⊗ F` has homology concentrated in `[a, b]`. -/
def torAmplitudeIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun M ↦ ∀ F : C, homologyConcentratedIn a b (M ⊗ (singleFunctor C 0).obj F)

variable {C}

/-- Widening the interval preserves Tor amplitude. -/
lemma torAmplitudeIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') {M : DerivedCategory C}
    (hM : torAmplitudeIn C a b M) : torAmplitudeIn C a' b' M :=
  fun F ↦ (hM F).mono ha hb

variable (C)

/-- An object of `D(C)` has *finite Tor amplitude* if it has Tor amplitude in some interval
`[a, b]`. -/
def finiteTorAmplitude : ObjectProperty (DerivedCategory C) :=
  fun M ↦ ∃ a b : ℤ, torAmplitudeIn C a b M

variable {C}

/-- Let `P` be a property of objects of `D(C)` that are bounded for the canonical t-structure.
An object satisfies `P` and has finite Tor amplitude exactly when, for some interval `[a, b]`,
it satisfies `P`, has homology concentrated in `[a, b]` and has Tor amplitude in `[a, b]`. -/
lemma exists_inf_homologyConcentratedIn_inf_torAmplitudeIn_iff
    {P : ObjectProperty (DerivedCategory C)} (hP : P ≤ TStructure.t.bounded)
    (K : DerivedCategory C) :
    (∃ a b : ℤ, (P ⊓ homologyConcentratedIn a b ⊓ torAmplitudeIn C a b) K) ↔
      (P ⊓ finiteTorAmplitude C) K := by
  constructor
  · rintro ⟨a, b, ⟨hPK, -⟩, hta⟩
    exact ⟨hPK, a, b, hta⟩
  · rintro ⟨hPK, a, b, hta⟩
    obtain ⟨c, d, hcd⟩ := (exists_homologyConcentratedIn_iff_bounded K).2 (hP K hPK)
    exact ⟨min a c, max b d, ⟨hPK, hcd.mono (min_le_right _ _) (le_max_right _ _)⟩,
      hta.mono (min_le_left _ _) (le_max_left _ _)⟩

end DerivedCategory
