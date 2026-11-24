/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingChains

/-! # Dimension of maximal localizations of finite type domains

Every maximal localization of a finite type domain over a field has the same Krull dimension
as the domain.

## References

* Stacks Project, Algebra, Lemma 00OS.
-/

@[expose] public section

universe u v

/-- Every maximal localization of a finite type domain over a field has the
same Krull dimension as the domain. -/
theorem finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    ∀ (m : Ideal S) [m.IsMaximal],
      ringKrullDim (Localization.AtPrime m) = ringKrullDim S := by
  obtain ⟨d, hd, hchains⟩ :=
    finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains (k := k) (S := S)
  have : FiniteRingKrullDim S :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr
      ⟨by simp [hd], by
        rw [hd]
        change ((d : ℕ∞) : WithBot ℕ∞) ≠ ((⊤ : ℕ∞) : WithBot ℕ∞)
        exact fun h ↦ ENat.natCast_ne_top d (WithBot.coe_injective h)⟩
  intro m hm
  obtain ⟨c, hlast, hlength⟩ := Ideal.exists_ltSeries_length_eq_height m
  have hfull : (c.length : ℕ∞) = Order.height c.last := by
    rw [hlast, ← PrimeSpectrum.height_eq_orderHeight]
    exact hlength
  have hsat : IsMin c.head ∧ ∀ i : Fin c.length, c i.castSucc ⋖ c i.succ := by
    have hind := Order.height_eq_index_of_length_eq_height_last hfull
    refine ⟨Order.height_eq_zero.mp (hind 0), ?_⟩
    intro i
    refine ⟨c.step i, ?_⟩
    intro x hprev hnext
    have h1 := Order.height_add_one_le hprev
    have h2 := Order.height_add_one_le hnext
    rw [hind i.castSucc] at h1
    rw [hind i.succ] at h2
    have h1' : ((i.val + 1 : ℕ) : ℕ∞) ≤ Order.height x := by simpa using h1
    have h2' : Order.height x + 1 ≤ ((i.val + 1 : ℕ) : ℕ∞) := by simpa using h2
    have h3 : ((i.val + 2 : ℕ) : ℕ∞) ≤ ((i.val + 1 : ℕ) : ℕ∞) := calc
      _ = ((i.val + 1 : ℕ) : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.height x + 1 := add_le_add h1' le_rfl
      _ ≤ _ := h2'
    have h4 : i.val + 2 ≤ i.val + 1 := by exact_mod_cast h3
    omega
  obtain ⟨hmin, hcov⟩ := hsat
  have hmax : IsMax c.last := by
    rw [hlast, PrimeSpectrum.isMax_iff]
    exact hm
  have hchain : IsMaxChain (fun x y : PrimeSpectrum S ↦ x ≤ y) (Set.range c) := by
    classical
    refine ⟨c.monotone.isChain_range, fun t ht hsub ↦ hsub.antisymm fun x hx ↦ ?_⟩
    by_contra hnot
    have hne (i : Fin (c.length + 1)) : c i ≠ x := fun h ↦ hnot ⟨i, h⟩
    have hlt : ∀ i, c i < x := by
      intro i
      induction i using Fin.induction with
      | zero =>
        exact (ht.lt_of_le (hsub ⟨0, rfl⟩) hx (hne 0)).resolve_right hmin.not_lt
      | succ i hi =>
        exact (ht.lt_of_le (hsub ⟨i.succ, rfl⟩) hx (hne i.succ)).resolve_right
          ((hcov i).2 hi)
    exact hmax.not_lt (hlt (Fin.last c.length))
  have hcd := hchains c hchain
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), hd,
    ← hlength, hcd]
  rfl

