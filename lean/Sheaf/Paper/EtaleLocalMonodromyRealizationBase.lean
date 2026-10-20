/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.Paper.NormalizedMonodromyFunctor
import Sheaf.Paper.NormalizedMonodromyExact

/-! # Simultaneous exact monodromy realizations

Source: Bhatt--Scholze, Corollary 6.8.5.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Normalized exact realizations can be chosen simultaneously on all pointed charts.
Source: Bhatt--Scholze, Corollary 6.8.5.
(blueprint: lem-sfb-etale-local-monodromy-realization-base) -/
theorem exists_sf_monodromy_realization (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    Nonempty (∀ (T : Scheme.{u}) (p : SfMonodromyPoint T), SfMonodromyRealization l E p) := by
  classical
  have H : ∀ (T : Scheme.{u}) (p : SfMonodromyPoint T),
      Nonempty (SfMonodromyRealization l E p) := by
    intro T p
    have : ConnectedSpace T := p.connected
    obtain ⟨c, _⟩ := galois_lisse_representations p.point p.group
    obtain ⟨J, ⟨hff⟩, hadd, hlin, hlisse, N, hN⟩ :=
      exists_sf_normalized_monodromy_functor l E T p c
    exact ⟨{
      finiteCorrespondence := c
      functor := J
      fullyFaithful := hff
      additive := hadd
      linear := hlin
      lisse := hlisse
      exact := sf_normalized_monodromy_exact l E T p c J hadd N hN
      normalization := N
      naturality := hN }⟩
  exact ⟨fun T p ↦ Classical.choice (H T p)⟩

end AlgebraicGeometry.Scheme
