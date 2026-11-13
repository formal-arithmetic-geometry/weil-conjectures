/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleAffineChartDescent
import Mathlib.Data.Finset.Order

/-!
# Descent of étaleness to a stage of an inverse limit

Source: Stacks Project, Limits, Lemma 07RP in Situation 081D.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism over a quasi-compact quasi-separated stage,
whose source and target are quasi-compact quasi-separated, is étale at some later stage
if its base change to the inverse limit is étale (Stacks, Tags 07RP and 081D). -/
theorem Etale.exists_stage_of_inverseLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : Etale (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (h : i₀ ≤ i),
      Etale (((Over.pullback (D.map (homOfLE h).op)).map f₀).left) := by
  classical
  have local_chart (x : X₀.left) :
      ∃ (U : X₀.left.Opens), x ∈ U ∧
        ∃ (i : I) (_ : i₀ ≤ i), ∀ (j : I) (_ : i ≤ j) (hj : i₀ ≤ j),
          Etale (((pullback.fst X₀.hom (D.map (homOfLE hj).op)) ⁻¹ᵁ U).ι ≫
            ((Over.pullback (D.map (homOfLE hj).op)).map f₀).left) := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := D.obj (op i₀)) (x := Y₀.hom (f₀.left x)) (U := ⊤) (by simp)
    obtain ⟨V, hV, hxV, eV⟩ := exists_isAffineOpen_mem_and_subset
      (X := Y₀.left) (x := f₀.left x) (U := Y₀.hom ⁻¹ᵁ W) hxW
    obtain ⟨U, hU, hxU, eU⟩ := exists_isAffineOpen_mem_and_subset
      (X := X₀.left) (x := x) (U := f₀.left ⁻¹ᵁ V) hxV
    refine ⟨U, hxU, Etale.exists_stage_on_affine_chart D c hc i₀ X₀ Y₀ f₀
      W hW V hV eV U hU eU ?_⟩
    have := hf
    infer_instance
  choose U hxU k hk hstage using local_chart
  have hcover : (Set.univ : Set X₀.left) ⊆ ⋃ x, (U x : Set X₀.left) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X₀.left)) (fun x ↦ (U x).isOpen) hcover
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨i, hi⟩ := (insert i₀ (s.image k)).exists_le
  have hi₀ : i₀ ≤ i := hi i₀ (Finset.mem_insert_self _ _)
  refine ⟨i, hi₀, ?_⟩
  let q := D.map (homOfLE hi₀).op
  have hU : (⨆ x : s, U x) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun x : s ↦ (pullback.fst X₀.hom q) ⁻¹ᵁ U x)
    ((pullback.fst X₀.hom q).iSup_preimage_eq_top hU)
  intro x
  exact hstage x i (hi (k x) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨x, x.property, rfl⟩))) hi₀

end AlgebraicGeometry
