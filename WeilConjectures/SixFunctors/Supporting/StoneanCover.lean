/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Compactification.StoneCech
public import WeilConjectures.ProEtaleCoefficients.CompactT2.StoneanProjective

/-!
# Stonean covers of compact Hausdorff spaces

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-stonean/det-pe-stonean-cover.md (blueprint: det-pe-stonean-cover).
-/

@[expose] public section

open Filter Function Topology

universe u

/-- The Stonean ultrafilter cover of a compact Hausdorff space.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-stonean/det-pe-stonean-cover.md (blueprint: det-pe-stonean-cover).

Proof, following the node's seven steps:
1. The compact-Hausdorff-basis dependency gives compactness, Hausdorffness,
and the clopen membership basis on `Ultrafilter T`.
2. A principal ultrafilter contains `E` exactly when its point belongs to `E`.
Every nonempty basic open has a nonempty defining set, hence contains a
principal ultrafilter. The basis therefore proves density.
3. Write an open set as a union of basic opens defined by sets `Eᵢ` and put
`E = ⋃ i, Eᵢ`. The union is contained in the closed basic set defined by `E`.
Conversely, a basic neighborhood defined by `F` of a point in that basic set
has `E ∩ F` in its proper filter. Choose a point of this nonempty intersection
and an index whose `Eᵢ` contains it. Its principal ultrafilter is in the
neighborhood and the original open set. Thus the closure is the basic set
of `E`, hence open. Empty unions give the empty set on both sides.
4. Apply `CompactT2.extremallyDisconnected_iff_projective_iff_section` to
obtain projectivity and total disconnectedness. Together with compactness
and Hausdorffness this is profiniteness.
5. The continuous-extension dependency applied to the identity on the
underlying set gives the map `Ultrafilter.extend (id : T → T)`, continuous
and equal to `t` at every principal ultrafilter `pure t`.
6. For an open neighborhood `V` of its value at `p`, continuity and the
membership basis give `E ∈ p` whose basic open maps into `V`. Evaluating
at principal ultrafilters shows `E ⊆ V`, so upward closure gives `V ∈ p`.
Thus `p` converges to that value in `T`.
7. Two distinct limits would have disjoint neighborhoods, both in the proper
ultrafilter, forcing the empty set into it. This proves uniqueness. Agreement
at `pure t` proves surjectivity and extension of the identity. If `T` is
empty there are no ultrafilters, and the empty map is still surjective.
-/
theorem stonean_cover
    (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T] :
    (CompactSpace (Ultrafilter T) ∧ T2Space (Ultrafilter T) ∧
      (∀ (E : Set T), IsClopen {p : Ultrafilter T | E ∈ p}) ∧
      DenseRange (pure : T → Ultrafilter T)) ∧
      (ExtremallyDisconnected (Ultrafilter T) ∧
        TotallyDisconnectedSpace (Ultrafilter T) ∧
        CompactT2.Projective (Ultrafilter T)) ∧
      (Continuous (Ultrafilter.extend (id : T → T)) ∧
        Surjective (Ultrafilter.extend (id : T → T)) ∧
        (∀ t : T, Ultrafilter.extend (id : T → T) (pure t) = t) ∧
      (∀ (p : Ultrafilter T) (x : T),
          (↑p : Filter T) ≤ 𝓝 x ↔ x = Ultrafilter.extend (id : T → T) p)) := by
  -- Shorten the closure argument in the plan: extend a lift from principal ultrafilters,
  -- then use density and Gleason's equivalence to obtain extremal disconnectedness.
  have hproj : CompactT2.Projective (Ultrafilter T) := by
    intro Y Z _ _ _ _ _ _ f g hf hg hgsur
    obtain ⟨s, hs⟩ := hgsur.hasRightInverse
    let t : T → Y := s ∘ f ∘ (pure : T → Ultrafilter T)
    let h : Ultrafilter T → Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend t
    refine ⟨h, hh, ?_⟩
    apply denseRange_pure.equalizer (hg.comp hh) hf
    funext x
    simpa [Function.comp_def, h, t] using hs (f (pure x))
  have hED : ExtremallyDisconnected (Ultrafilter T) :=
    (CompactT2.extremallyDisconnected_iff_projective_iff_section (Ultrafilter T)).1.mpr hproj
  have hTD : TotallyDisconnectedSpace (Ultrafilter T) :=
    (CompactT2.extremallyDisconnected_iff_projective_iff_section (Ultrafilter T)).2.2 hED
  have hclopen : ∀ (E : Set T), IsClopen {p : Ultrafilter T | E ∈ p} := by
    intro E
    exact ⟨ultrafilter_isClosed_basic E, ultrafilter_isOpen_basic E⟩
  have hcont : Continuous (Ultrafilter.extend (id : T → T)) :=
    continuous_ultrafilter_extend _
  have hpure : ∀ t : T, Ultrafilter.extend (id : T → T) (pure t) = t := by
    intro t
    exact ultrafilter_extend_pure _ _
  have hsurj : Surjective (Ultrafilter.extend (id : T → T)) := by
    intro t
    exact ⟨pure t, hpure t⟩
  have hlim : ∀ (p : Ultrafilter T) (x : T),
      (↑p : Filter T) ≤ 𝓝 x ↔ x = Ultrafilter.extend (id : T → T) p := by
    intro p x
    simpa only [Ultrafilter.map_id, eq_comm] using
      (ultrafilter_extend_eq_iff (f := id) (b := p) (c := x)).symm
  exact ⟨⟨inferInstance, inferInstance, hclopen, denseRange_pure⟩,
    ⟨hED, hTD, hproj⟩, ⟨hcont, hsurj, hpure, hlim⟩⟩

end
