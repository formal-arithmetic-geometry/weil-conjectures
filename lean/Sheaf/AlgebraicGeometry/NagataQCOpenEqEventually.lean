/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage

/-!
# Eventual equality of descended quasi-compact opens

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
sk-prop-nagata-sketch-approximation/lemma-nagata-qc-open-eq-eventually.md
(blueprint: lemma-nagata-qc-open-eq-eventually).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lemma-nagata-qc-open-eq-eventually) Above the stage selected by
`nagataQCOpenEqualityStage`, the pullbacks of the two compact opens agree.
Source: Stacks Project, Tag 01Z4 (2), applied to the base-changed inverse system;
blueprint node `lemma-nagata-qc-open-eq-eventually`, order 350.

Proof: unfold the stage definition. Its chosen witness is an object of
`baseChangeDiagram D p`, with underlying index τ, where the inverse images agree
by `exists_map_preimage_eq_map_preimage` (Stacks 01Z4 (2)). The map to the base
object identifies this equality with equality under the first pullback projection.
By `le_directedFiniteUpperBound` (node `lemma-nagata-directed-finite-upper-bound`)
and `hd`, both i₀ and τ lie below the selected stage. Hence any later j is above τ.
Pull the witness equality back along the transition map of `baseChangeDiagram D p`.
Its compatibility with the first projections and `Scheme.Hom.comp_preimage` give
the asserted equality on the pullback over j. This also covers the selected stage
itself. No chartwise presentation data from the superseded stage definition is used.
-/
theorem nagataQCOpenEqEventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) {Y₀ : Scheme.{u}} (p : Y₀ ⟶ D.obj (Opposite.op i₀))
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (W₁ W₂ : Y₀.Opens) (hW₁ : IsCompact (W₁ : Set Y₀))
    (hW₂ : IsCompact (W₂ : Set Y₀))
    (hEq : pullback.fst p (c.π.app (Opposite.op i₀)) ⁻¹ᵁ W₁ =
      pullback.fst p (c.π.app (Opposite.op i₀)) ⁻¹ᵁ W₂)
    (d : I → I → I) (hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j) (r : LinearOrder I) :
    ∀ (j : I) (h₀ : i₀ ≤ j),
      nagataQCOpenEqualityStage D c hc i₀ p W₁ W₂ hW₁ hW₂ hEq d r ≤ j →
      pullback.fst p (D.map (homOfLE h₀).op) ⁻¹ᵁ W₁ =
        pullback.fst p (D.map (homOfLE h₀).op) ⁻¹ᵁ W₂ := by
  sorry

end AlgebraicGeometry
