/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Descent of finite locally free morphisms

Source: Stacks Project, Limits, Lemma Tag 06AC, in Situation Tag 081D
(blueprint: lem-weil-pbc-descend-finite-locally-free).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite locally freeness, and its degree, descend to a finite stage of an inverse limit
of schemes with affine transition morphisms.

Source: Stacks Project, Limits, Lemma Tag 06AC, in Situation Tag 081D
(blueprint: lem-weil-pbc-descend-finite-locally-free).

Proof:
1. Locally finite presentation implies locally finite type by the finite generators in an
   affine presentation (def-sbc-locally-finite-presentation, def-weil-finite-type-morphism).
   Finite local freeness gives finiteness and flatness (def-pc-finite-locally-free).
   Descend these separately (lem-weil-pbc-descend-finite,
   lem-weil-pbc-descend-flat-finite-presentation), then choose a common later stage.
   Cartesian-square pasting identifies the maps there as base changes; finiteness,
   flatness and locally finite presentation persist (lem-weil-pbc-cartesian-square-pasting,
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence). Thus that stage is finite locally free.
2. If the limit map has degree d, take the clopen degree-d locus W in the stage target
   (lem-weil-pbc-finite-locally-free-degree-locally-constant). Rank base change and pasting
   show that the limit target maps into W (lem-weil-pbc-finite-flat-rank-iso,
   lem-weil-pbc-cartesian-square-pasting).
3. The limit target is the limit of the base-changed targets (lem-weil-pbc-scheme-over-limit).
   Their affine transitions and the qcqs initial target make them qcqs
   (lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence).
   The clopen W is retrocompact, hence constructible (def-weil-constructible-subset).
   A later target therefore maps into W (lem-weil-pbc-limit-contained-in-constructible).
4. At that later stage finite local freeness persists by the same base-change permanence
   and pasting as in Step 1. Rank base change identifies every fibre degree with the degree
   at its image in W, which is d (lem-weil-pbc-finite-flat-rank-iso).
   This is finite local freeness of degree d (def-pc-finite-locally-free).
-/
theorem descend_finite_locally_free
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (hf : Scheme.Hom.IsFiniteLocallyFree (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    (∃ (i : I) (hi : i₀ ≤ i),
      Scheme.Hom.IsFiniteLocallyFree (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left)) ∧
    (∀ d : ℕ,
      Scheme.Hom.IsFiniteLocallyFreeOfDegree
          (((Over.pullback (c.π.app (op i₀))).map f₀).left) d →
        ∃ (i : I) (hi : i₀ ≤ i),
          Scheme.Hom.IsFiniteLocallyFreeOfDegree
            (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) d) := by
  sorry

end AlgebraicGeometry
