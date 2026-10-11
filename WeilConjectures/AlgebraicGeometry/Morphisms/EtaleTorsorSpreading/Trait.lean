/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum

/-!
# The trait case of the spreading theorem

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, let `s ∈ S` be a point of codimension one, so that `𝒪_{S,s}` is a
discrete valuation ring. If the normalization `N ⟶ C` of `C` in the Galois cover is étale over
the generic point, it is étale over `σ(s)`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOverSection_of_coheight_eq_one`, tame
ramification and Abhyankar's lemma) and then over all of `C_s`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_coheight_eq_one`, purity). This is the
first paragraph of the proof of [Stacks 0EYJ].
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (trait case, near
the section; first paragraph of the proof of [Stacks 0EYJ]): over a Noetherian base, at a point
`s` of codimension one the normalization `N ⟶ C` is étale over `σ(s)`.

Proof sketch. Base change to `R = 𝒪_{S,s}`, a discrete valuation ring (normal Noetherian local
of dimension one); normalization commutes with this localization. Then `C_s ⊆ C` is an effective
Cartier divisor, regular as it is smooth over a field, and `C_η = C \ C_s`. At the generic point
`ξ` of `C_s` the local ring is a discrete valuation ring and all ramification indices of the
Galois cover are equal to one `e` dividing `|G|` ([Stacks 09EB]), hence invertible: `Z` is tamely
ramified over `C` in codimension one. By Abhyankar's lemma for a regular divisor ([Stacks 0EYG],
itself proved through the purity of the branch locus [Stacks 0BMB] on the regular scheme
`C[x]/(xᵉ - π)`) and [Stacks 0EYH], étale locally on `C` the normalization is a disjoint union of
`Spec A[x]/(x^{e_i} - f)` with `f` a local equation of `C_s`. The section is transversal to
`C_s` (`σ⁻¹(C_s)` is the reduced closed point), and the fibre of `Z` over `σ(η)` is a disjoint
union of copies of `Spec κ(η)` (it has a rational point and `G` acts simply transitively), so
the trait test [Stacks 0EYI] forces all `e_i = 1` near `σ(s)`: `N` is étale over a
neighbourhood of `σ(s)`. -/
theorem etaleOverSection_of_coheight_eq_one [IsNoetherian D.S] (s : D.S)
    (hs : Order.coheight s = 1) (hη : D.EtaleOver (genericPoint D.S)) :
    D.EtaleOverSection s :=
  sorry

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (trait case, purity;
first paragraph of the proof of [Stacks 0EYJ]): over a Noetherian base, at a point `s` of
codimension one, if the normalization `N ⟶ C` is étale over the generic point and over `σ(s)`,
it is étale over all of `C_s`.

Proof sketch. The étale locus of `N ⟶ C` is open; it contains the points over `σ(s)`, hence
(going up for the integral `N ⟶ C`) the points over the generic point of the fibre `C_s`, which
is irreducible (smooth with geometrically connected fibres) and specializes to `σ(s)`. So `N` is
unramified over `C` in codimension one. `C` is regular at the points of `C_s` (smooth over the
discrete valuation ring `𝒪_{S,s}`), and `N` is normal and finite over `C` (normalization of a
normal Noetherian scheme in a finite separable extension), so the purity of the branch locus
[Stacks 0BMB] (equivalently purity across the regular divisor `C_s`, [Stacks 0EYE]) shows that
`N` is étale at every point over `s`. -/
theorem etaleOver_of_coheight_eq_one [IsNoetherian D.S] (s : D.S)
    (hs : Order.coheight s = 1) (hη : D.EtaleOver (genericPoint D.S))
    (hsec : D.EtaleOverSection s) : D.EtaleOver s :=
  sorry

end AlgebraicGeometry.Scheme.SpreadingDatum
