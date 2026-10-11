/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Order.DirectedFiniteUpperBound
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Stage of equality for descended quasi-compact opens

Source: Stacks Project, Tag 01Z4 (2), and blueprint node
`def-nagata-qc-open-equality-stage`, chapter `sec-nagata-compactification`, order 349
(blueprint: def-nagata-qc-open-equality-stage).
The stage is selected geometrically by the proved compact-open equality descent theorem.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Classical in
/-- (blueprint: def-nagata-qc-open-equality-stage) In the base-changed inverse system,
select a stage where the pullbacks of two compact opens agree, using Stacks Tag 01Z4 (2),
and apply the selected finite upper bound to this stage and the base stage.
The selection uses the proved `exists_map_preimage_eq_map_preimage`; no unproved
finite-data theorem is used to construct data. -/
noncomputable def nagataQCOpenEqualityStage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) {Y₀ : Scheme.{u}} (p : Y₀ ⟶ D.obj (Opposite.op i₀))
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (W₁ W₂ : Y₀.Opens) (hW₁ : IsCompact (W₁ : Set Y₀))
    (hW₂ : IsCompact (W₂ : Set Y₀))
    (hEq : pullback.fst p (c.π.app (Opposite.op i₀)) ⁻¹ᵁ W₁ =
      pullback.fst p (c.π.app (Opposite.op i₀)) ⁻¹ᵁ W₂)
    (d : I → I → I) (r : LinearOrder I) : I :=
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
  directedFiniteUpperBound i₀ d r {i₀, (Classical.choose e).left.unop}

end AlgebraicGeometry
