/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum

/-!
# The case of depth at least two of the spreading theorem

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, let `s ∈ S` be a point of codimension at least two, so that `𝒪_{S,s}`
has depth at least two. If the normalization `N ⟶ C` of `C` in the Galois cover is étale over
all strict generizations of `s`, it is étale over `σ(s)`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOverSection_of_two_le_coheight`, through the
formal neighbourhood of the section) and then over all of `C_s`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_two_le_coheight`). This is the "proof of
the claim" in the proof of [Stacks 0EYJ].
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (depth at least two,
near the section; proof of the claim in [Stacks 0EYJ]): over a Noetherian base, at a point `s`
of codimension at least two, if the normalization `N ⟶ C` is étale over all strict
generizations of `s`, it is étale over `σ(s)`.

Proof sketch. Base change to `A = 𝒪_{S,s}` (normalization commutes with this localization); `U`
is the punctured spectrum of `A` and `N` is finite étale over `C_U`. As `A` is normal of dimension
at least two, `depth A ≥ 2` ([Stacks 031S]), and `depth 𝒪_{C,x} ≥ 2` for `x` over `s`
([Stacks 0337]); `N` is normal, so it is the finite `C`-scheme of [Stacks 0EY6] extending
`N|_{C_U}` with depth at least two along the complement, and its formation commutes with flat
base change. Choose an affine `Spec B ⊆ C` around `σ(s)`, so `A → B` is smooth with a section
`B → A` of kernel `I`; the `I`-adic completion is `B^ ≅ A[[x_1, …, x_d]]` ([Stacks 05D5]) and
`B → B^` is flat. Let `V ⊆ Spec B^` be the preimage of `U`, `W = N ×_C V`, and
`V_0 = V ∩ V(x_1, …, x_d) ≅ U`. Then `W_0 = W ×_V V_0 ⟶ U` is completely split: its generic
fibre is the fibre of `Z` over `σ(η)`, a disjoint union of copies of `Spec κ(η)`, and `U` is
normal. By the full faithfulness of `FÉt_V ⟶ FÉt_{V_0}` for power series over a local ring of
depth at least two ([Stacks 0EY9], which rests on `Γ(U, 𝒪_U) = A` in depth two [Stacks 0BK0], the
formal full faithfulness [Stacks 0EKP] and [Stacks 0EL8]), `W ≅ W_0 ×_U V` is split, hence so
is `N ×_C Spec B^`; by faithfully flat descent along `𝒪_{C,σ(s)} → B^` (localized at its maximal
ideal) `N` is étale over `σ(s)`. -/
theorem etaleOverSection_of_two_le_coheight [IsNoetherian D.S] (s : D.S)
    (hs : 2 ≤ Order.coheight s) (H : ∀ s' : D.S, s' ⤳ s → s' ≠ s → D.EtaleOver s') :
    D.EtaleOverSection s :=
  sorry

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (depth at least two,
extension over the fibre; proof of the claim in [Stacks 0EYJ]): over a Noetherian base, at a
point `s` of codimension at least two, if the normalization `N ⟶ C` is étale over all strict
generizations of `s` and over `σ(s)`, it is étale over all of `C_s`.

Proof sketch. The étale locus `E` of `N ⟶ C` is open, contains `C_U` (`U` the punctured
spectrum of `𝒪_{S,s}`) and the points over `σ(s)`, hence the generic point of the irreducible
fibre `C_s`, so `E ∩ C_s` is dense in `C_s`. By [Stacks 0EYB] (applied over `Spec 𝒪_{S,s}`,
whose points of depth at most one lie in `U`), `FÉt_C ⟶ FÉt_E` is an equivalence, so `N|_E`
extends to a finite étale `C`-scheme, which is normal and hence equal to the normalization
`N`. -/
theorem etaleOver_of_two_le_coheight [IsNoetherian D.S] (s : D.S)
    (hs : 2 ≤ Order.coheight s) (H : ∀ s' : D.S, s' ⤳ s → s' ≠ s → D.EtaleOver s')
    (hsec : D.EtaleOverSection s) : D.EtaleOver s :=
  sorry

end AlgebraicGeometry.Scheme.SpreadingDatum
