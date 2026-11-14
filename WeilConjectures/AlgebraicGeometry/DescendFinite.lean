/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.DescendAffine
import WeilConjectures.AlgebraicGeometry.DescendFiniteAffineOpen

/-!
# Finiteness descends to a finite stage of a limit

## References

* Stacks Project, Tag 01ZO (under Situation 081D)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem isAffineHom_over_pullback_iff
    {S T : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y) (q : T ⟶ S) :
    IsAffineHom
      (pullback.map (f.left ≫ Y.hom) q Y.hom q f.left (𝟙 T) (𝟙 S)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ↔
      IsAffineHom (((Over.pullback q).map f).left) := by
  let e := pullback.congrHom (Over.w f) (rfl : q = q)
  have he : pullback.map (f.left ≫ Y.hom) q Y.hom q f.left (𝟙 T) (𝟙 S)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      e.hom ≫ ((Over.pullback q).map f).left := by
    apply pullback.hom_ext <;>
      simp [e, Over.pullback_map_left, pullback.congrHom_hom, pullback.map]
  rw [he]
  exact MorphismProperty.cancel_left_of_respectsIso @IsAffineHom e.hom _

/-- Finiteness of a base change to an inverse limit descends to a finite stage
(Stacks, Tags 01ZO and 081D). -/
theorem exists_isFinite_baseChange_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hfinite : IsFinite (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsFinite (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  classical
  have hf : IsAffineHom (((Over.pullback (c.π.app (op i₀))).map f₀).left) :=
    hfinite.toIsAffineHom
  have hlim := (isAffineHom_over_pullback_iff X₀ Y₀ f₀ (c.π.app (op i₀))).mpr hf
  obtain ⟨k, hk, haffine⟩ :=
    exists_isAffineHom_baseChange_of_isLimit D c hc i₀ f₀.left Y₀.hom hlim
  have hak :=
    (isAffineHom_over_pullback_iff X₀ Y₀ f₀ (D.map (homOfLE hk).op)).mp haffine
  let 𝒰 := Y₀.left.affineCover.finiteSubcover
  have hlocal (b : 𝒰.I₀) :=
    exists_isFinite_morphismRestrict_baseChange_affine_open D c hc i₀ k hk X₀ Y₀ f₀
      hak (𝒰.f b).opensRange (isAffineOpen_opensRange (𝒰.f b))
      (IsZariskiLocalAtTarget.restrict (P := @IsFinite) hfinite _)
  choose j hj hfin using hlocal
  have : Nonempty I := ⟨k⟩
  obtain ⟨i, hi⟩ := (Set.finite_range j).bddAbove
  obtain ⟨i', hki', hii'⟩ := exists_ge_ge k i
  refine ⟨i', hk.trans hki', ?_⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun b : 𝒰.I₀ ↦ (pullback.fst Y₀.hom
      (D.map (homOfLE (hk.trans hki')).op)) ⁻¹ᵁ (𝒰.f b).opensRange)
  · simp only [← Scheme.Hom.preimage_iSup, 𝒰.iSup_opensRange,
      Scheme.Hom.preimage_top]
  · intro b
    exact hfin b i' ((hi (Set.mem_range_self b)).trans hii')

end AlgebraicGeometry
