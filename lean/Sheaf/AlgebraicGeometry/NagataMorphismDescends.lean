/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.NagataMorphismDescent

/-!
# The selected finite-stage morphism recovers the original morphism

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 354
(blueprint: lemma-nagata-morphism-descends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The glued morphism at the prescribed finite upper bound has base change `phi`.
Source: blueprint node order 354 (blueprint: lemma-nagata-morphism-descends).
The equation uses the canonical projections of `baseChangeCone`. Since `phi` and the
selected morphism are over their respective bases, the fibre-product universal property
identifies this equation with equality of the base-changed morphism and `phi`.

Proof:
1. By `lemma-nagata-qc-open-descends`, each selected descended open has inverse image
   W, the inverse image under phi of its target chart. Intersecting with the inverse
   image of T preserves W because phi is over S and the target chart lies over T.
   The affine refinements therefore pull back to a cover of W. Compatibility of the
   projections in `def-nagata-basechanged-system` preserves these opens at later stages.
2. On each affine refinement, the map on sections is the algebra map given by the
   lifted generators and vanishing relations. By `lemma-nagata-filtered-colimit-finite-data`
   and generatorLift_eq, its composite to limit sections agrees with phi on generators.
   Algebra maps agreeing on generators are equal, so the base-changed chart map is
   the restriction of phi. Transitivity of base change preserves this at the final stage.
3. The restrictions of `nagataMorphismDescent` are the transported chart maps, by
   `Scheme.Cover.ι_glueMorphisms`. Base change commutes with restriction to opens.
   The limit refinements cover X since the target charts cover Y. Thus the two maps
   agree on an open cover; open-cover extensionality gives the displayed equation. -/
theorem nagataMorphismDescends
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} {hc : IsLimit c}
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    {p : X₀ ⟶ D.obj (op i₀)} {q : Y₀ ⟶ D.obj (op i₀)}
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    {phi : (baseChangeCone D c p).pt ⟶ (baseChangeCone D c q).pt}
    {d : I → I → I} {hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j} {r : LinearOrder I}
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) :
    (baseChangeCone D c p).π.app
        (Over.mk (homOfLE (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.1).op) ≫
      (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.2.left =
    phi ≫ (baseChangeCone D c q).π.app
        (Over.mk (homOfLE (nagataMorphismDescent D c hc i₀ p q phi d hd r data).2.1).op) := by
  sorry

end AlgebraicGeometry
