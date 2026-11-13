/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleStageSectionCocone
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLiftAffine
import WeilConjectures.AlgebraicGeometry.EtaleAffineSectionSameStageEquality
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The canonical cocone of affine étale section sets

## References

* Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YN
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The cocone of stagewise sections of `G` over an étale object, along an affine-transition
limit of qcqs schemes, is a colimit cocone (Stacks, Tag 09YQ). -/
theorem etaleStageSectionCocone_isColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    [IsAffine W₀.left] : Nonempty (IsColimit (etaleStageSectionCocone D c i₀ G W₀)) := by
  classical
  let F := etaleStageSectionDiagram D c i₀ G W₀
  let C := etaleStageSectionCocone D c i₀ G W₀
  refine ⟨Types.FilteredColimit.isColimitOf' F C ?_ ?_⟩
  · intro t
    obtain ⟨j, s, hs⟩ := etaleSetSectionLift_affine D c hc i₀ G W₀ t
    exact ⟨op j, s, hs.symm⟩
  · intro j s t hst
    obtain ⟨k, a, ha⟩ := etaleAffineSection_sameStageEquality D c hc i₀ G W₀
      j.unop s t hst
    exact ⟨op k, a.op, ha⟩

end AlgebraicGeometry
