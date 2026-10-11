/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Sheaf.Order.DirectedFiniteUpperBound

/-!
# Finite-stage model of a quasi-compact open

Source: blueprint, sec-nagata-compactification, sk-prop-nagata-sketch-approximation,
node order 347 (blueprint: def-nagata-qc-open-descent).

The choices of affine charts, basic-open presentations, and finite-stage lifts are inputs.
The output computes the selected common stage and the union of transported basic opens.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Compatibility of inverse-image charts with a base-change transition.
Source: blueprint node order 347 (blueprint: def-nagata-qc-open-descent).
Proof: `baseChangeDiagram_map_fst` identifies the composite with the projection to the
original scheme. Taking inverse images of the chart gives the equality, hence the inclusion.
This is the well-definedness proof needed for transporting chart sections. -/
theorem nagataQCOpenDescent_chart_le
    {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    {i : J} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    {j k : Over i} (t : j ⟶ k) (U : Y.Opens) :
    pullback.fst p (D.map j.hom) ⁻¹ᵁ U ≤
      (baseChangeDiagram D p).map t ⁻¹ᵁ (pullback.fst p (D.map k.hom) ⁻¹ᵁ U) := by
  sorry

/-- Compatibility of inverse-image charts with a base-changed limit projection.
Source: blueprint node order 347 (blueprint: def-nagata-qc-open-descent).
Proof: `baseChangeCone_π_app_fst` identifies the composite projection to the original
scheme. The inverse image of an open along a composite is the iterated inverse image.
Thus the two chart opens are equal, and the required inclusion follows. -/
theorem nagataQCOpenDescent_limit_chart_le
    {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u}) (c : Cone D)
    {i : J} {Y : Scheme.{u}} (p : Y ⟶ D.obj i) (j : Over i) (U : Y.Opens) :
    pullback.fst p (c.π.app i) ⁻¹ᵁ U ≤
      (baseChangeCone D c p).π.app j ⁻¹ᵁ (pullback.fst p (D.map j.hom) ⁻¹ᵁ U) := by
  sorry

/-- The finite-stage open obtained from the chosen finite affine cover and basic-open lifts.
Source: blueprint node order 347 (blueprint: def-nagata-qc-open-descent).

`stage` and `lift` are the stages and representatives chosen using
`CommRingCat.exists_finite_data_stage` with zero equalities after identifying the chart's
section ring with its filtered colimit (`nonempty_isColimit_Γ_mapCocone`).
The common stage is `directedFiniteUpperBound` of the base stage and the chart stages.
The inequalities needed to transport sections use `le_directedFiniteUpperBound`.
The union depends on these choices; eventual independence is the second clause of
`exists_map_preimage_eq_map_preimage` (node `pqf-lem-limit-qc-open-descends`).
The limit and affine-transition assumptions justify obtaining the choices, rather than
changing the formula for an already chosen family. -/
noncomputable def nagataQCOpenDescent
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (_hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) {Y₀ : Scheme.{u}} (p : Y₀ ⟶ D.obj (op i₀))
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (W : (baseChangeCone D c p).pt.Opens)
    (_hW : IsCompact (W : Set (baseChangeCone D c p).pt))
    (m : ℕ) (U : Fin m → Y₀.Opens) (_hU : ∀ a, IsAffineOpen (U a))
    (_hcover : iSup U = ⊤) (r : Fin m → ℕ)
    (f : ∀ a, Fin (r a) → Γ((baseChangeCone D c p).pt,
      pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a))
    (_hpresentation : ∀ a, W ⊓ (pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a) =
      ⨆ k, (baseChangeCone D c p).pt.basicOpen (f a k))
    (stage : Fin m → I) (ha : ∀ a, i₀ ≤ stage a)
    (lift : ∀ a, Fin (r a) →
      Γ((baseChangeDiagram D p).obj (Over.mk (homOfLE (ha a)).op),
        pullback.fst p (D.map (homOfLE (ha a)).op) ⁻¹ᵁ U a))
    (_hlift : ∀ a k,
      ((baseChangeCone D c p).π.app (Over.mk (homOfLE (ha a)).op)).appLE
        (pullback.fst p (D.map (homOfLE (ha a)).op) ⁻¹ᵁ U a)
        (pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a)
        (nagataQCOpenDescent_limit_chart_le D c p
          (Over.mk (homOfLE (ha a)).op) (U a)) (lift a k) = f a k)
    (d : I → I → I) (hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j)
    (order : LinearOrder I) :
    Σ' w : I, Σ' hw : i₀ ≤ w,
      ((baseChangeDiagram D p).obj (Over.mk (homOfLE hw).op)).Opens :=
  letI : DecidableEq I := Classical.decEq I
  let F : Finset I := insert i₀ (Finset.univ.image stage)
  let w := directedFiniteUpperBound i₀ d order F
  let hw : i₀ ≤ w :=
    le_directedFiniteUpperBound i₀ d hd order (Finset.mem_insert_self _ _)
  let hwa : ∀ a, stage a ≤ w := fun a ↦
    le_directedFiniteUpperBound i₀ d hd order
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  let j : Over (op i₀) := Over.mk (homOfLE hw).op
  let t : ∀ a, j ⟶ Over.mk (homOfLE (ha a)).op := fun a ↦
    Over.homMk (homOfLE (hwa a)).op (Subsingleton.elim _ _)
  ⟨w, hw, ⨆ a, ⨆ k, ((baseChangeDiagram D p).obj j).basicOpen
    (((baseChangeDiagram D p).map (t a)).appLE
      (pullback.fst p (D.map (homOfLE (ha a)).op) ⁻¹ᵁ U a)
      (pullback.fst p (D.map j.hom) ⁻¹ᵁ U a)
      (nagataQCOpenDescent_chart_le D p (t a) (U a)) (lift a k))⟩

end AlgebraicGeometry
