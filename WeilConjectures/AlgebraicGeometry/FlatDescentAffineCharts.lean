/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.FlatDescentChart
import WeilConjectures.AlgebraicGeometry.FlatDescentChartComparison

/-!
# Affine charts for flatness descent

## References

* Stacks Project, Tag 04AI
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem finite_affine_triples {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [CompactSpace X] :
    ∃ n : ℕ, ∃ (W : Fin n → S.Opens) (V : Fin n → Y.Opens)
      (U : Fin n → X.Opens),
      (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (V b)) ∧
      (∀ b, IsAffineOpen (U b)) ∧ (∀ b, V b ≤ g ⁻¹ᵁ W b) ∧
      (∀ b, U b ≤ f ⁻¹ᵁ V b) ∧ (∀ x : X, ∃ b, x ∈ U b) := by
  classical
  have h (x : X) : ∃ (W : S.Opens) (V : Y.Opens) (U : X.Opens),
      IsAffineOpen W ∧ IsAffineOpen V ∧ IsAffineOpen U ∧
      V ≤ g ⁻¹ᵁ W ∧ U ≤ f ⁻¹ᵁ V ∧ x ∈ U := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (show g (f x) ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ g ⁻¹ᵁ W from hxW)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨W, V, U, hW, hV, hU, hVW, hUV, hxU⟩
  choose W V U hW hV hU hVW hUV hx using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, (fun b ↦ W (e.symm b)), (fun b ↦ V (e.symm b)),
    (fun b ↦ U (e.symm b)), (fun b ↦ hW _), (fun b ↦ hV _), (fun b ↦ hU _),
    (fun b ↦ hVW _), (fun b ↦ hUV _), ?_⟩
  intro x
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨e ⟨y, hyt⟩, by simpa using hxy⟩

/-- A finite family of affine triples translates flatness over the limit to flatness of
colimit tensor-product maps, and translates flatness of all stage maps back to scheme
flatness. This is only the affine reduction, with no eventual flatness assertion
(Stacks, Tag 04AI and Situation 081D). -/
theorem exists_flat_descent_affine_charts
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left] :
    ∃ n : ℕ, ∃ charts : Fin n →
      FlatDescentChart {i : I // i₀ ≤ i} ⟨i₀, le_rfl⟩,
      (Flat (((Over.pullback (c.π.app (op i₀))).map f₀).left) →
        ∀ b, (charts b).limitFlat) ∧
      (∀ j : {i : I // i₀ ≤ i},
        (∀ b, (charts b).stageFlat j j.property) →
        Flat (((Over.pullback (D.map (homOfLE j.property).op)).map f₀).left)) := by
  classical
  obtain ⟨n, W, V, U, hW, hV, hU, hVW, hUV, hcover⟩ :=
    finite_affine_triples f₀.left Y₀.hom
  have hcharts (b : Fin n) := exists_flat_descent_chart_comparison D c hc i₀ X₀ Y₀ f₀
    (W b) (V b) (U b) (hW b) (hV b) (hU b) (hVW b) (hUV b)
  choose charts hstage hlimit using hcharts
  refine ⟨n, charts, ?_, ?_⟩
  · intro hf b
    let := (charts b).sourceAlgebra
    let := (charts b).targetAlgebra
    let := (colimit.ι (charts b).rings ⟨i₀, le_rfl⟩).hom.toAlgebra
    obtain ⟨Vl, Ul, h, ⟨e⟩⟩ := hlimit b
    let R : CommRingCat.{u} := colimit (charts b).rings
    change (Algebra.TensorProduct.map (Algebra.ofId R R) (charts b).map).toRingHom.Flat
    exact Flat.SpecMap_iff.mp <| (MorphismProperty.arrow_mk_iso_iff (@Flat) e).mp
      (IsZariskiLocalAtSource.resLE h hf)
  · intro j hf
    apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @Flat)).mpr
    intro x
    obtain ⟨b, hxb⟩ := hcover ((pullback.fst X₀.hom
      (D.map (homOfLE j.property).op)) x)
    let := (charts b).sourceAlgebra
    let := (charts b).targetAlgebra
    let := ((charts b).rings.map
      (homOfLE (show (⟨i₀, le_rfl⟩ : {i : I // i₀ ≤ i}) ≤ j from j.property))).hom.toAlgebra
    obtain ⟨Vj, Uj, h, hUj, ⟨e⟩⟩ := hstage b j
    refine ⟨Vj, Uj, ?_, h, ?_⟩
    · rw [hUj]
      exact hxb
    · exact (MorphismProperty.arrow_mk_iso_iff (@Flat) e).mpr
        (Flat.SpecMap_iff.mpr (hf b))

end AlgebraicGeometry
