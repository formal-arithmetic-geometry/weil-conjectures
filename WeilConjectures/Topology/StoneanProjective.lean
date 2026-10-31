/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.ExtremallyDisconnected

/-!
# Gleason's characterization of Stonean spaces

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-stonean/det-pe-stonean-projective.md
(blueprint: det-pe-stonean-projective).
-/

@[expose] public section

universe u

open Function

namespace CompactT2

/-- For a compact Hausdorff space, extremal disconnectedness, projectivity for
compact Hausdorff surjections, and the existence of sections of all such
surjections are equivalent.  An extremally disconnected space is also totally
disconnected and therefore is a profinite space with its given compact
Hausdorff structure.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-pe-stonean/det-pe-stonean-projective.md (blueprint: det-pe-stonean-projective).

The same characterization is Stacks Project, Topology, Tag 08YN; total
disconnectedness and profiniteness follow Tags 08YI and 08ZY.

Proof:
1. Mathlib's `CompactT2.projective_iff_extremallyDisconnected` proves Gleason's
characterization, following the same minimal closed surjecting source argument.
2. Projectivity gives a section by lifting the identity map.
3. Conversely, given a continuous surjection `p : X → Y` and a continuous
`f : S → Y`, the equalizer `P = {(s,x) | f(s) = p(x)}` is closed in the
compact Hausdorff product `S × X`. Its first projection is continuous and
surjective. A section of that projection, followed by the second projection,
is a continuous lift of `f` through `p`.
4. Mathlib supplies total separatedness of extremally disconnected Hausdorff
spaces, which implies total disconnectedness. -/
theorem extremallyDisconnected_iff_projective_iff_section
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S] :
    (ExtremallyDisconnected S ↔ CompactT2.Projective S) ∧
      (CompactT2.Projective S ↔
        ∀ (P : Type u) [TopologicalSpace P] [CompactSpace P] [T2Space P]
          (q : P → S), Continuous q → Surjective q →
            ∃ σ : S → P, Continuous σ ∧ q ∘ σ = id) ∧
      (ExtremallyDisconnected S → TotallyDisconnectedSpace S) := by
  refine ⟨CompactT2.projective_iff_extremallyDisconnected.symm, ⟨?_, ?_⟩, ?_⟩
  · intro h P _ _ _ q hq hsurj
    exact h continuous_id hq hsurj
  · intro h X Y _ _ _ _ _ _ f p hf hp hsurj
    let P : Set (S × X) := {z | f z.1 = p z.2}
    have : CompactSpace P := isCompact_iff_compactSpace.mp
      (isClosed_eq (hf.comp continuous_fst) (hp.comp continuous_snd)).isCompact
    let q : P → S := fun z ↦ z.val.1
    have hq : Continuous q := continuous_fst.comp continuous_subtype_val
    have hqsurj : Surjective q := by
      intro s
      obtain ⟨x, hx⟩ := hsurj (f s)
      exact ⟨⟨(s, x), hx.symm⟩, rfl⟩
    obtain ⟨σ, hσ, hsec⟩ := h P q hq hqsurj
    refine ⟨fun s ↦ (σ s).val.2,
      continuous_snd.comp (continuous_subtype_val.comp hσ), ?_⟩
    funext s
    calc
      p (σ s).val.2 = f (σ s).val.1 := (σ s).property.symm
      _ = f s := congrArg f (congr_fun hsec s)
  · intro h
    let := h
    infer_instance

end CompactT2
