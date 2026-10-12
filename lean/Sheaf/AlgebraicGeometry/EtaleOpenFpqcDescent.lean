/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!
# Descent of opens in an etale base change of an fpqc covering

Source: Stacks Project, Descent, Tag 03N0, applied as in Etale Cohomology, Tag 09XN
(blueprint: lem-weil-pbc-etale-open-fpqc-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Tag 03N0, applied in the proof of Tag 09XN
(blueprint: lem-weil-pbc-etale-open-fpqc-descent).
Compatible opens in the base changes of an etale scheme along an fpqc covering descend
uniquely. The overlap `(T i ×[S] V) ×[V] (T j ×[S] V)` is canonically
`T i ×[S] T j ×[S] V`, and its projections are the maps used for compatibility.

Proof:
1. By fpqc base-change stability (`lem-galois-fpqc-covering-base-change`, Tag 022D), the
   second projections `T i ×[S] V ⟶ V` form an fpqc covering.
2. Apply compatible-open descent (`lem-weil-pbc-open-subscheme-fpqc-descent`, Tag 03N0)
   to this covering. The fibre-product universal property (`def-pc-fibre-product`)
   identifies its double overlaps with the triple products in the hypothesis. This
   gives the unique open of `V` whose inverse images are the specified opens. -/
theorem existsUnique_open_of_etale_fpqc_baseChange
    {S V : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (f : V ⟶ S) [Etale f] (W : ∀ i, (pullback (g i) f).Opens)
    (hcompat : ∀ i j,
      (pullback.fst (pullback.snd (g i) f) (pullback.snd (g j) f)) ⁻¹ᵁ W i =
        (pullback.snd (pullback.snd (g i) f) (pullback.snd (g j) f)) ⁻¹ᵁ W j) :
    ∃! U : V.Opens, ∀ i, (pullback.snd (g i) f) ⁻¹ᵁ U = W i := by
  have hcover' :
      Presieve.ofArrows (fun i => pullback (g i) f)
          (fun i => pullback.snd (g i) f) ∈ Scheme.fpqcPrecoverage V := by
    rw [Presieve.ofArrows_pullback]
    exact Precoverage.pullbackArrows_mem f hcover
  exact openSubscheme_existsUnique_of_fpqc
    (g := fun i => pullback.snd (g i) f) hcover' W hcompat

end AlgebraicGeometry
