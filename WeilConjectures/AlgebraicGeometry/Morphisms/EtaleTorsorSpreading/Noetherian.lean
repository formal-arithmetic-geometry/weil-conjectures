/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.DepthTwo
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.GenericPoint
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Trait

/-!
# The spreading theorem over a Noetherian base

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, the relative normalization `N ⟶ C` of `C` in the Galois cover `Z.P` is
finite étale and restricts to `Z.P` over the generic fibre
(`AlgebraicGeometry.Scheme.SpreadingDatum.exists_isFinite_etale_isPullback`). This is
[Stacks 0EYJ].

The proof is an induction on the codimension of the points `s ∈ S`, replacing the maximal open
argument of [Stacks 0EYJ]: if `N` is étale over all strict generizations of `s`, it is étale over
`s` (`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_forall_specializes`), by the generic
case, the trait case (codimension one) or the case of depth at least two.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- The induction step of the proof of [Stacks 0EYJ]: if the normalization `N ⟶ C` is étale
over all strict generizations of `s`, it is étale over `s`. -/
theorem etaleOver_of_forall_specializes [IsNoetherian D.S] (s : D.S)
    (H : ∀ s' : D.S, s' ⤳ s → s' ≠ s → D.EtaleOver s') : D.EtaleOver s := by
  by_cases hη : s = genericPoint D.S
  · exact hη ▸ D.etaleOver_genericPoint
  have hgen : D.EtaleOver (genericPoint D.S) :=
    H _ ((genericPoint_spec D.S).specializes (Set.mem_univ s)) (Ne.symm hη)
  have h0 := coheight_ne_zero_of_ne_genericPoint s hη
  by_cases h1 : Order.coheight s = 1
  · exact D.etaleOver_of_coheight_eq_one s h1 hgen
      (D.etaleOverSection_of_coheight_eq_one s h1 hgen)
  · have h2 : 2 ≤ Order.coheight s := by
      induction h : Order.coheight s using ENat.recTopCoe with
      | top => simp
      | coe n => rw [h] at h0 h1; norm_cast at *; omega
    exact D.etaleOver_of_two_le_coheight s h2 H (D.etaleOverSection_of_two_le_coheight s h2 H)

/-- Over a Noetherian base the normalization `N ⟶ C` is étale over every point of `S`: by
induction on the codimension, which is finite and drops under strict generization. -/
theorem forall_etaleOver [IsNoetherian D.S] (s : D.S) : D.EtaleOver s := by
  have hfin (x : D.S) : Order.coheight x < ⊤ := by
    have := ringKrullDim_lt_top (R := D.S.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight] at this
    exact WithBot.coe_lt_coe.1 this
  suffices ∀ n : ℕ, ∀ x : D.S, Order.coheight x = n → D.EtaleOver x by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hfin s).ne
    exact this n s hn.symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    refine D.etaleOver_of_forall_specializes x fun s' hs' hne ↦ ?_
    have hlt : x < s' := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hs')
      fun h ↦ hne (Inseparable.eq ((Scheme.le_iff_specializes.1 h).antisymm hs')).symm
    have := Order.coheight_strictAnti hlt (hfin s')
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hfin s').ne
    rw [hx, ← hm] at this
    exact ih m (by exact_mod_cast this) s' hm.symm

/-- Over a Noetherian base the normalization of `C` in the Galois cover is étale over `C`. -/
theorem etale_fromNormalization [IsNoetherian D.S] : Etale D.ν.fromNormalization :=
  D.etale_fromNormalization_of_forall_etaleOver D.forall_etaleOver

/-- [Stacks 0EYJ], without the Galois structure: over a Noetherian base the Galois cover `Z.P` of
the generic fibre extends to a finite étale `C`-scheme, namely the normalization of `C` in it. -/
@[stacks 0EYJ]
theorem exists_isFinite_etale_isPullback [IsNoetherian D.S] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ D.C) (_ : IsFinite p) (_ : Etale p) (ψ : D.Z.P ⟶ Y),
      IsPullback ψ D.Z.π p D.j :=
  D.exists_isFinite_etale_isPullback_of_forall_etaleOver D.forall_etaleOver

end AlgebraicGeometry.Scheme.SpreadingDatum
