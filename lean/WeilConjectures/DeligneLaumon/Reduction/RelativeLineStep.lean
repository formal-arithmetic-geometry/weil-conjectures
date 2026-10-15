/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The relative affine-line step of the Deligne–Laumon reduction

For the projection `p : 𝔸¹_S ⟶ S` of the relative affine line over a separated `k₀`-scheme of
finite type, `Rʳp₀!F` is mixed of weights at most `w + r` whenever the Weil sheaf `F` is mixed of
weights at most `w`, and `Rp₀!` preserves Weil complexes mixed of weights at most `w`. Iterating,
the same holds for the projection of the `r`-fold relative affine line.

The proof stratifies a punctually pure sheaf on `𝔸¹_S`: its pieces are either separated
quasi-finite over `S`, or opens of a relative affine line `𝔸¹_V` over a locally closed `V ⊆ S`
with surjective projection on which the sheaf is lisse, and they are glued by open–closed
decompositions. The direct-image bound holds on each piece — by the quasi-finite lemma, resp. by
the relative affine-line proposition `sk-p-dl-general-relative-line` — and passes through the
gluing by the long exact sequences of the open–closed triangles.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.HasRelativeLineStratification`: a stratification of a Weil sheaf
  over `S` into quasi-finite pieces and pure lisse relative-line pieces, glued along open–closed
  decompositions.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification`: blueprint
  `thm-zl-relative-line-stratification`.
- `AlgebraicGeometry.hasDirectImageWeightBound_affineLine` and
  `AlgebraicGeometry.hasDirectImageComplexWeightBound_affineLine`: blueprint
  `thm-zl-relative-line-step`, in its sheaf and its complex form.
- `AlgebraicGeometry.hasDirectImageWeightBound_iteratedAffineLineProj`: the bound for the
  projection of the iterated relative affine line.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §3.3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

section Stratification

variable (ι) (w : ℝ) {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf `F` on a `k₀`-scheme `X` over `S` (through `h : X ⟶ S`) *has a relative-line
stratification with pure pieces of weight `w`* if it is built, by finitely many open–closed
decompositions `U ↪ X ↩ Z` of the source, from pieces of the following two kinds:

- `h` is separated and quasi-finite, and `F` is mixed of weights at most `w`;
- `h` factors as an open immersion `v : X ⟶ 𝔸¹_V` with surjective projection to `V`, followed by
  the projection `𝔸¹_V ⟶ V` and an immersion `c : V ⟶ S`, and `F` is lisse and punctually pure of
  weight `w`:

```
X --- v ---> 𝔸¹_V --- ↘ ---> V --- c ---> S
```

(blueprint: `thm-zl-relative-line-stratification`, the finite stratifications of source and target
refined to open–closed filtrations). -/
inductive WeilSheaf.HasRelativeLineStratification :
    ∀ {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))], WeilSheaf k₀ l X → Prop
  /-- A separated quasi-finite piece. -/
  | quasiFinite {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated h] [LocallyQuasiFinite h]
      [LocallyOfFiniteType h] [QuasiCompact h] (F : WeilSheaf k₀ l X)
      (hF : F.IsMixedOfWeightsAtMost ι w) :
      WeilSheaf.HasRelativeLineStratification h F
  /-- A piece open in a relative affine line, carrying a lisse sheaf punctually pure of
  weight `w`. -/
  | affineLine {X V : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [V.Over (Spec (CommRingCat.of k₀))] [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] (v : X ⟶ 𝔸(PUnit.{u + 1}; V))
      [IsOpenImmersion v] [QuasiCompact v] [v.IsOver (Spec (CommRingCat.of k₀))]
      (hv : Surjective (v ≫ 𝔸(PUnit.{u + 1}; V) ↘ V)) (c : V ⟶ S) [IsImmersion c]
      [QuasiCompact c] [c.IsOver (Spec (CommRingCat.of k₀))] (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))] (hh : h = (v ≫ 𝔸(PUnit.{u + 1}; V) ↘ V) ≫ c)
      (F : WeilSheaf k₀ l X) (hF : F.IsLisse) (hpure : F.IsPunctuallyPureOfWeight ι w) :
      WeilSheaf.HasRelativeLineStratification h F
  /-- Gluing along an open immersion `j` and its closed complement `i`. -/
  | openClosed {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType
  (U ↘ Spec (CommRingCat.of k₀))]
      [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
      (j : U ⟶ X)
      [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X)
      [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
      (hij : IsCompl (Set.range j.base) (Set.range i.base)) (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
      WeilSheaf.HasRelativeLineStratification (j ≫ h) ((WeilSheaf.upperStar j).obj F) →
      WeilSheaf.HasRelativeLineStratification (i ≫ h) ((WeilSheaf.upperStar i).obj F) →
      WeilSheaf.HasRelativeLineStratification h F

variable [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (S ↘ Spec (CommRingCat.of k₀))]

variable {ι w} in
/-- If `F` has a relative-line stratification over `S` with pure pieces of weight `w`, then
`Rʳh₀!F` is mixed of weights at most `w + r` for every `r`: on a quasi-finite piece by
`sk-l-dl-general-quasifinite`, on a relative-line piece by `sk-p-dl-general-relative-line`
composed with the quasi-finite immersion `c`, and through the gluing by the exact sequences of
the open–closed triangles (blueprint: `thm-zl-relative-line-step`, the reassembly of the
strata). -/
theorem WeilSheaf.HasRelativeLineStratification.isMixedOfWeightsAtMost
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {h : X ⟶ S}
    [h.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (H : F.HasRelativeLineStratification ι w h) :
    ∀ [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] (r : ℕ),
      ((WeilSheaf.higherLowerShriek k₀ l h r).obj F).IsMixedOfWeightsAtMost ι (w + r) := by
  induction H with
  | quasiFinite h F hF =>
    exact fun r ↦ HasDirectImageWeightBound.of_locallyQuasiFinite h w F hF r
  | affineLine v hv c h hh F hF hpure =>
    subst hh
    exact fun r ↦ WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp
      (isMixedOfWeightsAtMost_higherLowerShriek_of_affineLine ι v hv F hF w hpure)
      (.of_locallyQuasiFinite c) r
  | openClosed j i hij h F _ _ ihU ihZ =>
    intro _ _ _ r
    obtain ⟨S', hS', ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
      WeilSheaf.exists_exact_higherLowerShriek_of_openClosed (f := h) hij F r
    exact (WeilSheaf.IsMixedOfWeightsAtMost.of_exact hS' ((ihU r).of_iso e₁.symm)
      ((ihZ r).of_iso e₃.symm)).of_iso e₂

end Stratification

variable {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (S ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]

instance : LocallyOfFiniteType (𝔸(PUnit.{u + 1}; S) ↘ Spec (CommRingCat.of k₀)) := by
  rw [← CategoryTheory.comp_over (𝔸(PUnit.{u + 1}; S) ↘ S) (Spec (CommRingCat.of k₀))]
  infer_instance

/-- Let `S` be a separated `k₀`-scheme of finite type and `F` a Weil sheaf on the relative affine
line `𝔸¹_S`, punctually `ι`-pure of weight `w`. Then `F` has a relative-line stratification over
`S` with pure pieces of weight `w`: there are finite stratifications of source and target, refined
to open–closed filtrations, such that each source stratum is either separated quasi-finite over
its target stratum, or open in its relative affine line with surjective projection and carries a
lisse restriction of `F` (blueprint: `thm-zl-relative-line-stratification`).

Over an integral affine open `Spec B` of `S`, the complement of the lissity locus of `F` is cut
out by an ideal of `B[T]` containing a nonzero polynomial; over the principal open of its leading
coefficient it is finite, and its complement is open in the relative affine line with nonempty
fibres. Noetherian induction on `S` covers the rest. -/
theorem WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification {w : ℝ}
    {F : WeilSheaf k₀ l 𝔸(PUnit.{u + 1}; S)} (hF : F.IsPunctuallyPureOfWeight ι w) :
    F.HasRelativeLineStratification ι w (𝔸(PUnit.{u + 1}; S) ↘ S) :=
  sorry

variable (S) in
/-- For the projection `p : 𝔸¹_S ⟶ S` of the relative affine line over a separated `k₀`-scheme
of finite type and a Weil sheaf `F` on `𝔸¹_S` mixed of weights at most `w`, the sheaf `Rʳp₀!F` is
mixed of weights at most `w + r`, for every `r` (blueprint: `thm-zl-relative-line-step`, sheaf
form).

The weight filtration of `F` and the long exact sequences of `Rp₀!` reduce to a punctually pure
graded piece, which has a relative-line stratification
(`WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification`). -/
theorem hasDirectImageWeightBound_affineLine :
    HasDirectImageWeightBound k₀ ι (𝔸(PUnit.{u + 1}; S) ↘ S) := by
  intro w F hF r
  obtain ⟨n, G, φ, h0, hlast, hmono, hpure⟩ := hF
  -- Induction along the filtration, whose successive quotients are punctually pure.
  have key : ∀ (i : ℕ) (hi : i < n + 1) (r : ℕ),
      ((WeilSheaf.higherLowerShriek k₀ l (𝔸(PUnit.{u + 1}; S) ↘ S) r).obj
        (G ⟨i, hi⟩)).IsMixedOfWeightsAtMost ι (w + r) := by
    intro i
    induction i with
    | zero =>
      exact fun _ r ↦ WeilSheaf.isMixedOfWeightsAtMost_of_isZero (Functor.map_isZero _ h0) _
    | succ i ih =>
      intro hi
      have := hmono ⟨i, by omega⟩
      obtain ⟨v, hv, hvpure⟩ := hpure ⟨i, by omega⟩
      exact WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_of_shortExact _
        (.mk' (ShortComplex.cokernelSequence_exact (φ ⟨i, by omega⟩)) this inferInstance)
        (ih (by omega)) fun r ↦
          (hvpure.hasRelativeLineStratification.isMixedOfWeightsAtMost r).mono_weight
            (by linarith)
  exact (key n (by omega) r).of_iso ((WeilSheaf.higherLowerShriek k₀ l _ r).mapIso hlast.some)

variable (S) in
/-- For the projection `p : 𝔸¹_S ⟶ S` of the relative affine line over a separated `k₀`-scheme
of finite type and a Weil complex `K` on `𝔸¹_S` mixed of weights at most `w`, the complex `Rp₀!K`
is mixed of weights at most `w` (blueprint: `thm-zl-relative-line-step`).

By `lem-zl-sheaves-to-complexes` this follows from the sheaf form
`AlgebraicGeometry.hasDirectImageWeightBound_affineLine`. -/
theorem hasDirectImageComplexWeightBound_affineLine :
    HasDirectImageComplexWeightBound k₀ ι (𝔸(PUnit.{u + 1}; S) ↘ S) :=
  fun _ _ hK ↦ (hasDirectImageWeightBound_affineLine S).isMixedOfWeightsAtMost_derivedLowerShriek hK

variable (S) in
/-- The direct-image weight assertion holds for the projection of the `r`-fold relative affine line
over a separated `k₀`-scheme of finite type, the composition of `r` affine-line projections
(blueprint: `thm-zl-relative-line-step` and `sk-l-dl-general-composition`). -/
theorem hasDirectImageWeightBound_iteratedAffineLineProj :
    ∀ (r : ℕ) [(iteratedAffineLine S r).Over (Spec (CommRingCat.of k₀))]
      [(iteratedAffineLineProj S r).IsOver (Spec (CommRingCat.of k₀))],
      HasDirectImageWeightBound k₀ ι (iteratedAffineLineProj S r)
  | 0, _, _ =>
    have : LocallyQuasiFinite (iteratedAffineLineProj S 0) :=
      inferInstanceAs (LocallyQuasiFinite (𝟙 S))
    have : LocallyOfFiniteType (iteratedAffineLine S 0 ↘ Spec (CommRingCat.of k₀)) := by
      rw [← CategoryTheory.comp_over (iteratedAffineLineProj S 0) (Spec (CommRingCat.of k₀))]
      infer_instance
    .of_locallyQuasiFinite (iteratedAffineLineProj S 0)
  | r + 1, ⟨hom⟩, h => by
    -- `iteratedAffineLine S (r + 1)` is the affine line over `iteratedAffineLine S r`, with the
    -- structure morphism through `iteratedAffineLineProj S r`.
    let : (iteratedAffineLine S r).Over (Spec (CommRingCat.of k₀)) :=
      ⟨iteratedAffineLineProj S r ≫ S ↘ Spec (CommRingCat.of k₀)⟩
    have : (iteratedAffineLineProj S r).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : IsSeparated (iteratedAffineLine S r ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (IsSeparated (iteratedAffineLineProj S r ≫ _))
    have : LocallyOfFiniteType (iteratedAffineLine S r ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (iteratedAffineLineProj S r ≫ _))
    have : QuasiCompact (iteratedAffineLine S r ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (QuasiCompact (iteratedAffineLineProj S r ≫ _))
    have H := (hasDirectImageWeightBound_affineLine (ι := ι) (iteratedAffineLine S r)).comp
      (hasDirectImageWeightBound_iteratedAffineLineProj r)
    obtain rfl : hom = iteratedAffineLineProj S (r + 1) ≫ S ↘ Spec (CommRingCat.of k₀) :=
      h.1.symm
    simpa [iteratedAffineLineProj_succ] using H

end AlgebraicGeometry
