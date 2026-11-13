/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.RingTheory.ColimitFlatRingMap
import WeilConjectures.AlgebraicGeometry.FlatDescentAffineCharts

/-!
# Descent of flatness to a finite stage

Source: Stacks Project, Limits of Schemes, Tag 04AI in Situation 081D.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Flatness of a locally finitely presented morphism over a quasi-compact quasi-separated
stage descends from a directed inverse limit with affine transitions to some later stage.
The source and target at the original stage are also quasi-compact and quasi-separated.

Source: Stacks Project, Limits of Schemes, Tag 04AI in Situation 081D. -/
theorem exists_flat_stage_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (hflat : Flat (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      Flat (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  classical
  let J := {i : I // i₀ ≤ i}
  let j₀ : J := ⟨i₀, le_rfl⟩
  let : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let : Nonempty J := ⟨j₀⟩
  obtain ⟨n, charts, hlimit, hstage⟩ :=
    exists_flat_descent_affine_charts D c hc i₀ X₀ Y₀ f₀
  have hevent (b : Fin n) : ∃ j : J, ∀ k : J, ∀ h : j ≤ k,
      (charts b).stageFlat k k.property := by
    let a := charts b
    let := a.sourceAlgebra
    let := a.targetAlgebra
    obtain ⟨j, hj, h⟩ := RingHom.exists_eventually_flat_of_colimit_flat
      a.rings j₀ a.source a.target a.map a.finitePresentation (hlimit hflat b)
    exact ⟨j, fun k hk ↦ h k hk⟩
  choose j hj using hevent
  obtain ⟨k, hk⟩ := (Finset.univ.image j).exists_le
  have hbound : ∀ b : Fin n, j b ≤ k := by
    intro b
    exact hk (j b) (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
  exact ⟨k.val, k.property, hstage k (fun b ↦ hj b k (hbound b))⟩

end AlgebraicGeometry
