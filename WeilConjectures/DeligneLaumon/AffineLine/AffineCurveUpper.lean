/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Fiber
public import WeilConjectures.DeligneLaumon.AffineLine.Purity
public import WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
public import WeilConjectures.DeligneLaumon.AffineLine.Upper
public import WeilConjectures.DeligneLaumon.Reduction.CompactSupport
public import WeilConjectures.WeilSheaf.UpperStarPointwise

/-!
# The compact-support upper bound on affine curves

Let `C₀` be a smooth geometrically connected affine curve over `k₀ = 𝔽_q` and `𝓕` a lisse Weil
sheaf on `C₀`, punctually `ι`-pure of weight `w`. Then `H_c^i(C, 𝓕)` has weights at most `w + i`
(blueprint: `thm-a1-affine-curve-upper`).

The degree-one bound is reduced to the Deligne–Laumon estimate on the affine line for a sheaf
unramified at infinity (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one`):

* the boundary sequence of `j : U₀ ↪ 𝔸¹` passes from `H_c^1(𝔸¹, j_*𝓔)` to `H_c^1(U, 𝓔)`, the
  boundary contributing weights at most `w`;
* finitely many points may be removed from the curve: `H_c^1` of the smaller open surjects onto
  `H_c^1` of the larger one.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite`:
  blueprint `lem-a1-finite-boundary-weights`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_sheaf`:
  the degree-one bound on `U₀` for a sheaf unramified at infinity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

/-- **Weights of the cohomology of a finite boundary.** Let `Z` be finite over `k₀` and `𝓖` a
Weil sheaf on `Z` whose stalks have weights at most `w`. Then `H_c^0(Z, 𝓖)` has weights at most
`w`. (blueprint: `lem-a1-finite-boundary-weights`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [IsFinite (Z ↘ Spec (CommRingCat.of k₀))]
    {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l Z} {w : ℝ} (hG : G.HasWeightsAtMost ι w) :
    (G.compactlySupportedCohomology 0).HasWeightsAtMostOver k₀ ι w := by
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
    (Z ↘ Spec (CommRingCat.of k₀)) G 0
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E.symm
    (WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite _ hG).compactlySupportedCohomology_zero

end WeilSheaf

namespace WeilSheaf.LisseOnDenseOpen

/-- The complement of the dense open `U₀` in the affine line is finite. -/
theorem finite_compl_range (D : LisseOnDenseOpen k₀ l) :
    ((Set.range D.j.base)ᶜ).Finite := by
  have hd : Dense (D.j.opensRange : Set (affineLine k₀)) := D.isDominant.denseRange
  obtain ⟨b, ⟨s, hs⟩, hb⟩ :=
    AffineSpace.exists_basicOpen_forall_exists_mem_and_finite D.j.opensRange hd.nonempty
  exact (hb s hs).2.subset fun x hx ↦ ⟨hx, Subsingleton.elim _ _⟩

variable (ι : PadicAlgCl l →+* ℂ)

/-- **Degree one on the open, unramified at infinity.** Let `𝓔` be lisse on the dense open
`U₀ ⊆ 𝔸¹`, punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^1(U, 𝓔)` has
weights at most `w + 1`: the boundary sequence
`H_c^0(Z, i^*j_*𝓔) → H_c^1(U, 𝓔) → H_c^1(𝔸¹, j_*𝓔)` of `j`, the affine-line estimate for the
middle extension, and the boundary semicontinuity of weights. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_sheaf (D : LisseOnDenseOpen k₀ l)
    (hinf : D.IsUnramifiedAtInfinity) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.sheaf.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  obtain ⟨Z, _, i, _, _, hrange, _⟩ :=
    Scheme.Opens.exists_isClosedImmersion_isFinite_compl (k₀ := k₀) D.j.opensRange
      (by simpa [Scheme.Hom.coe_opensRange] using D.finite_compl_range)
  have hij : Set.range i.base = (Set.range D.j.base)ᶜ := by
    rw [hrange, Scheme.Hom.coe_opensRange]
  obtain ⟨⟨δ, g, hex, -, hδ, hg⟩, -⟩ :=
    exists_exact_compactlySupportedCohomology_boundary D.j i hij D.sheaf D.lisse
  -- the middle extension on the line: the affine-line estimate
  have hA := D.hasWeightsAtMostOver_compactlySupportedCohomology_one ι hinf hw
  rw [directImage_eq] at hA
  -- the boundary: weights at most `w`
  have hd := D.hasWeightsAtMost_directImage hw.hasWeightsAtMost
  rw [directImage_eq] at hd
  have hB := WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite
    (hd.upperStar i)
  exact FrobeniusModule.HasWeightsAtMost.of_functionExact δ g hδ hg hex
    (hB.mono Nat.card_pos (by linarith)) hA

end WeilSheaf.LisseOnDenseOpen

namespace WeilSheaf

variable (ι : PadicAlgCl l →+* ℂ)

/-- **Degree one on an open of the line, unramified at infinity**, for an unbundled open immersion
`j : U₀ ↪ 𝔸¹`: if `𝓔` is lisse on `U₀`, punctually `ι`-pure of weight `w` and unramified at
infinity, then `H_c^1(U, 𝓔)` has weights at most `w + 1`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity
    {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    {E : WeilSheaf k₀ l U} (hE : E.IsLisse) (hinf : E.IsUnramifiedAtInfinity j) {w : ℝ}
    (hw : E.IsPunctuallyPureOfWeight ι w) :
    (E.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) :=
  LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_sheaf ι
    ⟨U, j, E, hE⟩ hinf hw

variable {ι}

/-- **Degree one on an open of the line, through a quasi-finite map to `ℙ¹`.** Let `𝓕` be lisse on
the dense open `U₀ ⊆ 𝔸¹`, punctually `ι`-pure of weight `w`, and let `H : U₀ ⟶ ℙ¹` be a separated
quasi-finite morphism and `W ⊆ ℙ¹` an open containing `∞`, with finite complement, on which
`H₀!𝓕` is lisse. Then `H_c^1(U, 𝓕)` has weights at most `w + 1`:
`H_c^1(U, 𝓕) = H_c^1(ℙ¹, H₀!𝓕)` is a quotient of `H_c^1(W, 𝓖)`, `𝓖 = (H₀!𝓕)|_W`, which is a quotient
of `H_c^1(V, 𝓖|_V)` for the part `V = W ∩ 𝔸¹` of `W` in the affine chart; and `𝓖|_V` is unramified
at infinity, since it extends to the lisse sheaf `𝓖` on `W ∋ ∞`. This replaces the constant field
extension and the homography of the blueprint (`lem-a1-unramified-at-infinity`). -/
theorem LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_of_projectiveLine
    (D : LisseOnDenseOpen k₀ l) (H : D.U ⟶ ProjectiveLine (Spec (CommRingCat.of k₀)))
    [H.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated H] [LocallyQuasiFinite H]
    [LocallyOfFiniteType H] [QuasiCompact H]
    (W : (ProjectiveLine (Spec (CommRingCat.of k₀))).Opens)
    (hWtop : (ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))).opensRange ⊔ W = ⊤)
    (hWfin : ((W : Set (ProjectiveLine (Spec (CommRingCat.of k₀))))ᶜ).Finite)
    (hG : ((upperStar W.ι).obj ((higherLowerShriek k₀ l H 0).obj D.sheaf)).IsLisse)
    {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.sheaf.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  sorry

end WeilSheaf

end AlgebraicGeometry
