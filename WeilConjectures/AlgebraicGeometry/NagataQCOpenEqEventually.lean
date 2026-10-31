/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NagataQCOpenEqualityStage
import WeilConjectures.Order.DirectedFiniteUpperBound
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual equality of descended quasi-compact opens

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
sk-prop-nagata-sketch-approximation/lemma-nagata-qc-open-eq-eventually.md
(blueprint: lemma-nagata-qc-open-eq-eventually).
-/

@[expose] public section

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
  classical
  let B := baseChangeDiagram D p
  let b := baseChangeCone D c p
  let j₀ : Over (Opposite.op i₀) := Over.mk (𝟙 (Opposite.op i₀))
  let f₀ := pullback.fst p (D.map j₀.hom)
  let e := exists_map_preimage_eq_map_preimage B b (isLimitBaseChangeCone D c p hc)
    (i := j₀)
    (U := f₀ ⁻¹ᵁ W₁) (V := f₀ ⁻¹ᵁ W₂)
    (QuasiCompact.isCompact_preimage (f := f₀) (W₁ : Set Y₀) W₁.isOpen hW₁)
    (QuasiCompact.isCompact_preimage (f := f₀) (W₂ : Set Y₀) W₂.isOpen hW₂)
    (by simpa [B, b, j₀, f₀, ← Scheme.Hom.comp_preimage] using hEq)
  let k := Classical.choose e
  obtain ⟨f, hf⟩ := Classical.choose_spec e
  have hk : pullback.fst p (D.map k.hom) ⁻¹ᵁ W₁ =
      pullback.fst p (D.map k.hom) ⁻¹ᵁ W₂ := by
    simpa only [f₀, ← Scheme.Hom.comp_preimage, B, baseChangeDiagram_map_fst] using hf
  intro j h₀ hj
  have hkj : k.left.unop ≤ j := le_trans
    (le_directedFiniteUpperBound i₀ d hd r
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self k.left.unop))) hj
  let t : Over.mk ((homOfLE h₀).op) ⟶ k :=
    Over.homMk (homOfLE hkj).op (Subsingleton.elim _ _)
  have ht := congrArg (fun W ↦ B.map t ⁻¹ᵁ W) hk
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage] at ht
  rw [show B.map t ≫ pullback.fst p (D.map k.hom) =
      pullback.fst p (D.map (homOfLE h₀).op) by
    exact baseChangeDiagram_map_fst D p t] at ht
  dsimp [B, baseChangeDiagram] at ht
  exact ht

end AlgebraicGeometry
