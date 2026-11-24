/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventually affine stages in an inverse system

## References

* Stacks Project, Tag 09ZM
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- If an inverse system of quasi-compact, quasi-separated schemes over a
quasi-compact, quasi-separated base has affine transition maps and affine
limit morphism, then all sufficiently late structure morphisms are affine
(Stacks, Tag 09ZM). -/
theorem eventually_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj T)
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsAffineHom f] :
    ∃ i : I, ∀ j : I, i ≤ j → IsAffineHom (h.app (op j)) := by
  classical
  let b : Iᵒᵖ := op (Classical.choice inferInstance)
  let 𝒰 := T.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  let V (a : 𝒰.I₀) : T.affineOpens := ⟨(𝒰.f a).opensRange,
    isAffineOpen_opensRange (𝒰.f a)⟩
  have H (a : 𝒰.I₀) : ∃ k : Over b, IsAffineOpen (h.app k.left ⁻¹ᵁ (V a).1) := by
    let U := h.app b ⁻¹ᵁ (V a).1
    have : QuasiCompact (h.app b) := by
      change QuasiCompact (show D.obj b ⟶ T from h.app b)
      infer_instance
    have hU : IsCompact (U : Set (D.obj b)) :=
      QuasiCompact.isCompact_preimage (f := h.app b) _ (V a).1.isOpen (V a).2.isCompact
    have (k : Over b) : CompactSpace ((opensDiagram D b U).obj k) :=
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage (f := D.map k.hom) _ U.isOpen hU)
    have (k : Over b) : QuasiSeparatedSpace ((opensDiagram D b U).obj k) :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map k.hom ⁻¹ᵁ U).isOpen).mp
        (.of_quasiSeparatedSpace _)
    have : IsAffine (opensCone D c b U).pt := by
      change IsAffineOpen (c.π.app b ⁻¹ᵁ U)
      simpa [U, ← Scheme.Hom.comp_preimage, _hf b] using (V a).2.preimage f
    obtain ⟨k, hk⟩ := Scheme.exists_isAffine_of_isLimit
      (opensDiagram D b U) (opensCone D c b U) (isLimitOpensCone D c _hc b U)
    refine ⟨k, ?_⟩
    change IsAffineOpen (D.map k.hom ⁻¹ᵁ U) at hk
    simpa [U, ← Scheme.Hom.comp_preimage, h.naturality k.hom] using hk
  choose k hk using H
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image (fun a ↦ (k a).left))
  have gi (a : 𝒰.I₀) : i ⟶ (k a).left := (hi (by simp)).some
  refine ⟨i.unop, fun j hij ↦ ?_⟩
  let g : op j ⟶ i := (homOfLE hij).op
  apply HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom) V 𝒰.iSup_opensRange
  intro a
  change IsAffineOpen (h.app (op j) ⁻¹ᵁ (V a).1)
  have ha := (hk a).preimage (D.map (g ≫ gi a))
  simpa [← Scheme.Hom.comp_preimage, h.naturality (g ≫ gi a)] using ha

end AlgebraicGeometry
