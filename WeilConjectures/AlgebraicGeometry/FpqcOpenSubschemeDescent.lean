/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.FpqcDetectsOpenness

/-!
# Fpqc descent of compatible open subschemes

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- Compatible open subschemes descend uniquely along an fpqc covering
(Stacks, Descent, Lemma 03N0). -/
theorem openSubscheme_existsUnique_of_fpqc
    {S : Scheme.{u}} {I : Type v} {T : I → Scheme.{u}}
    (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (W : ∀ i, (T i).Opens)
    (hW : ∀ (i j : I),
      (pullback.fst (g i) (g j) ⁻¹ᵁ W i) =
        (pullback.snd (g i) (g j) ⁻¹ᵁ W j)) :
    ∃! V : S.Opens, ∀ i, (g i ⁻¹ᵁ V) = W i := by
  let V : Set S := {s | ∃ i, ∃ x ∈ W i, g i x = s}
  have hpre (i : I) : g i ⁻¹' V = (W i : Set (T i)) := by
    ext x
    constructor
    · rintro ⟨j, y, hy, hxy⟩
      obtain ⟨z, hz₁, hz₂⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := g i) (g := g j) x y hxy.symm
      have hz : z ∈ pullback.snd (g i) (g j) ⁻¹ᵁ W j := by
        change pullback.snd (g i) (g j) z ∈ W j
        rwa [hz₂]
      rw [← hW i j] at hz
      change pullback.fst (g i) (g j) z ∈ W i at hz
      rwa [hz₁] at hz
    · intro hx
      exact ⟨i, x, hx, rfl⟩
  have hV : IsOpen V := isOpen_of_fpqc_preimages g hg V fun i => by
    rw [hpre i]
    exact (W i).isOpen
  let U : S.Opens := ⟨V, hV⟩
  refine ⟨U, ?_, ?_⟩
  · intro i
    apply SetLike.ext'
    exact hpre i
  · intro U' hU'
    apply SetLike.ext
    intro s
    obtain ⟨Y, f, hf, x, hx⟩ := Scheme.JointlySurjective.exists_eq
      (K := Scheme.precoverage @Flat) (Presieve.ofArrows T g) hg.2 s
    obtain ⟨i⟩ := hf
    have hi : g i ⁻¹ᵁ U = W i := by
      apply SetLike.ext'
      exact hpre i
    rw [← hx]
    change x ∈ g i ⁻¹ᵁ U' ↔ x ∈ g i ⁻¹ᵁ U
    rw [hU' i, hi]

end AlgebraicGeometry
