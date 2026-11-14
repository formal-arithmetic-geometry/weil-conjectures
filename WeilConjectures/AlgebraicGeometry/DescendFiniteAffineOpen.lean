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
import WeilConjectures.AlgebraicGeometry.DescendFiniteAffineBasePiece

/-!
# Local finiteness descent over one affine target open

## References

* Stacks Project, Tags 01ZO and 07RG
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem over_pullback_square {S T : Scheme.{u}}
    (X Y : Over S) (f : X ⟶ Y) (a : T ⟶ S) :
    IsPullback (pullback.fst X.hom a) (((Over.pullback a).map f).left)
      f.left (pullback.fst Y.hom a) := by
  have HX : IsPullback (pullback.fst X.hom a) (pullback.snd X.hom a)
      (f.left ≫ Y.hom) a := by
    simpa only [Over.w f] using IsPullback.of_hasPullback X.hom a
  have HY := IsPullback.of_hasPullback Y.hom a
  have H := IsPullback.of_bot' HX HY
  have he : (((Over.pullback a).map f).left) =
      HY.lift (pullback.fst X.hom a ≫ f.left) (pullback.snd X.hom a) (by
        simp [pullback.condition]) := by
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst, HY.lift_fst]
    · simp only [Over.pullback_map_left, pullback.lift_snd, HY.lift_snd]
  rw [he]
  exact H
private theorem finite_restrict_baseChange_comp
    {S T R : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    (a : T ⟶ S) (b : R ⟶ T) (V : Y.left.Opens)
    (hf : IsFinite ((((Over.pullback a).map f).left) ∣_
      ((pullback.fst Y.hom a) ⁻¹ᵁ V))) :
    IsFinite ((((Over.pullback (b ≫ a)).map f).left) ∣_
      ((pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V)) := by
  let x : pullback X.hom (b ≫ a) ⟶ pullback X.hom a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
      simp only [Category.assoc, pullback.condition])
  let y : pullback Y.hom (b ≫ a) ⟶ pullback Y.hom a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
      simp only [Category.assoc, pullback.condition])
  let fa := ((Over.pullback a).map f).left
  let fq := ((Over.pullback (b ≫ a)).map f).left
  have hcomm : x ≫ fa = fq ≫ y := by
    apply pullback.hom_ext <;> simp [x, y, fa, fq, Over.pullback_map_left]
  have hs : IsPullback x fq fa y := by
    apply IsPullback.of_right (t := over_pullback_square X Y f a)
    · simpa [x, y, fq] using over_pullback_square X Y f (b ≫ a)
    · exact hcomm
  have hpre : y ⁻¹ᵁ ((pullback.fst Y.hom a) ⁻¹ᵁ V) =
      (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage]
    simp [y]
  have hsource : x ⁻¹ᵁ fa ⁻¹ᵁ ((pullback.fst Y.hom a) ⁻¹ᵁ V) =
      fq ⁻¹ᵁ (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hcomm, Scheme.Hom.comp_preimage, hpre]
  have hr := Scheme.Hom.isPullback_resLE hs
    (US := (pullback.fst Y.hom a) ⁻¹ᵁ V)
    (UT := (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V)
    (UX := fa ⁻¹ᵁ (pullback.fst Y.hom a) ⁻¹ᵁ V)
    (UY := fq ⁻¹ᵁ (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V)
    hpre.ge le_rfl (by rw [hsource, inf_of_le_left (Scheme.Hom.preimage_mono _ le_rfl)])
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hr
  exact MorphismProperty.of_isPullback (P := @IsFinite) hr hf

private theorem isFinite_morphismRestrict_of_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    {B : Type*} (U : B → Y.Opens) (hle : ∀ b, U b ≤ V)
    (hcover : V ≤ ⨆ b, U b) (hfin : ∀ b, IsFinite (f ∣_ U b)) :
    IsFinite (f ∣_ V) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun b ↦ V.ι ⁻¹ᵁ U b)
  · apply top_unique
    intro x hx
    have hx' := hcover x.property
    simpa only [Scheme.Hom.preimage_iSup, Scheme.Hom.mem_preimage,
      TopologicalSpace.Opens.mem_iSup, Scheme.Opens.ι_apply] using hx'
  · intro b
    apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U b))).mpr
    have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U b) = U b := by
      simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hle b)]
    rw [he]
    exact hfin b

/-- Finiteness on one affine target open descends once an affine stage is known
(Stacks, Tags 01ZO and 07RG). -/
theorem exists_isFinite_morphismRestrict_baseChange_affine_open
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j), ∀ (i : I) (hji : j ≤ i),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans (hkj.trans hji))).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom
            (D.map (homOfLE (hk.trans (hkj.trans hji))).op)) ⁻¹ᵁ V)) := by
  classical
  have hnbhd (x : V) : ∃ (U : Y₀.left.Opens), IsAffineOpen U ∧ x.val ∈ U ∧
      U ≤ V ∧ ∃ W : (D.obj (op i₀)).Opens, IsAffineOpen W ∧ U ≤ Y₀.hom ⁻¹ᵁ W := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := D.obj (op i₀)) (x := Y₀.hom x.val) (U := ⊤) (by trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (U := V ⊓ Y₀.hom ⁻¹ᵁ W) ⟨x.property, hxW⟩
    exact ⟨U, hU, hxU, le_trans hUV inf_le_left, W, hW, le_trans hUV inf_le_right⟩
  choose U hU hxU hUV W hW hUW using hnbhd
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x ↦ (U x : Set Y₀.left))
    (fun x ↦ (U x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hlocal (b : t) :=
    exists_isFinite_morphismRestrict_baseChange_affine_base_piece D c hc i₀ k hk
      X₀ Y₀ f₀ haffine (U b.val) (hU b.val) (W b.val) (hW b.val) (hUW b.val)
      (by
        let p := pullback.fst Y₀.hom (c.π.app (op i₀))
        have H := IsZariskiLocalAtTarget.restrict (P := @IsFinite) hfinite
          ((p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U b.val))
        have he : (p ⁻¹ᵁ V).ι ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U b.val)) =
            p ⁻¹ᵁ U b.val := by
          rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
          exact inf_eq_right.mpr (p.preimage_mono (hUV b.val))
        have H' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
          (morphismRestrictRestrict _ _ _)).mp H
        rw [he] at H'
        exact H')
  choose j hj hfin using hlocal
  have : Nonempty I := ⟨k⟩
  obtain ⟨l, hl⟩ := (Set.finite_range j).bddAbove
  obtain ⟨l', hkl', hll'⟩ := exists_ge_ge k l
  refine ⟨l', hkl', ?_⟩
  intro i hli
  apply isFinite_morphismRestrict_of_cover _ _
    (fun b : t ↦ (pullback.fst Y₀.hom
      (D.map (homOfLE (hk.trans (hkl'.trans hli))).op)) ⁻¹ᵁ U b.val)
  · intro b
    exact Scheme.Hom.preimage_mono _ (hUV b.val)
  · intro x hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp (ht hx)
    obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hxb
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hb⟩, hxb⟩
  · intro b
    have hji := ((hl (Set.mem_range_self b)).trans hll').trans hli
    have H := finite_restrict_baseChange_comp X₀ Y₀ f₀
      (D.map (homOfLE (hk.trans (hj b))).op) (D.map (homOfLE hji).op)
      (U b.val) (hfin b)
    have he : D.map (homOfLE hji).op ≫ D.map (homOfLE (hk.trans (hj b))).op =
        D.map (homOfLE (hk.trans (hkl'.trans hli))).op := by
      rw [← D.map_comp]
      congr 1
    rw [he] at H
    exact H

end AlgebraicGeometry
