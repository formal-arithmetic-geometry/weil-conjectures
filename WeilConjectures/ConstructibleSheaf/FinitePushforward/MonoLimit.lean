/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Locally constant functions on cofiltered limits of schemes

Let `{Dᵢ}` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition morphisms and `X = lim Dᵢ`. An open and closed subset of `X` is the preimage of an
open and closed subset of some stage, so a locally constant function on `X` factors through a
locally constant function on some stage
(`AlgebraicGeometry.Scheme.exists_isLocallyConstant_eq_comp_of_isLimit`); a locally constant
function on a stage vanishing on `X` vanishes on some later stage
(`AlgebraicGeometry.Scheme.exists_comp_eq_zero_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- **Open and closed subsets of a limit come from a stage.** -/
theorem exists_isClopen_preimage_eq_of_isLimit {s : Set c.pt} (hs : IsClopen s) :
    ∃ (i : I) (W : Set (D.obj i)), IsClopen W ∧ c.π.app i ⁻¹' W = s := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let U : c.pt.Opens := ⟨s, hs.isOpen⟩
  let U' : c.pt.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  obtain ⟨i, V, hV, hVU⟩ := exists_preimage_eq D c hc U hs.isClosed.isCompact
  obtain ⟨j, V', hV', hVU'⟩ := exists_preimage_eq D c hc U' hs.isOpen.isClosed_compl.isCompact
  obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let A := D.map fki ⁻¹ᵁ V
  let B := D.map fkj ⁻¹ᵁ V'
  have hA : c.π.app k ⁻¹ᵁ A = U := by rw [← Scheme.Hom.comp_preimage, c.w, hVU]
  have hB : c.π.app k ⁻¹ᵁ B = U' := by rw [← Scheme.Hom.comp_preimage, c.w, hVU']
  have hAc : IsCompact (A : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V.2 hV
  have hBc : IsCompact (B : Set (D.obj k)) := QuasiCompact.isCompact_preimage _ V'.2 hV'
  obtain ⟨l, flk, hl⟩ := exists_map_preimage_eq_map_preimage D c hc (U := A ⊓ B) (V := ⊥)
    (QuasiSeparatedSpace.inter_isCompact _ _ A.2 hAc B.2 hBc) isCompact_empty (by
      rw [Scheme.Hom.preimage_inf, hA, hB, Scheme.Hom.preimage_bot]
      ext x
      simp [U, U'])
  obtain ⟨l', fl'k, hl'⟩ := exists_map_preimage_eq_map_preimage D c hc (U := A ⊔ B) (V := ⊤)
    (hAc.union hBc) isCompact_univ (by
      rw [Scheme.Hom.preimage_sup, hA, hB, Scheme.Hom.preimage_top]
      ext x
      simp [U, U'])
  obtain ⟨m, a, b, hab⟩ := IsCofiltered.cospan flk fl'k
  let W := D.map (a ≫ flk) ⁻¹ᵁ A
  let W' := D.map (a ≫ flk) ⁻¹ᵁ B
  have hinf : W ⊓ W' = ⊥ := by
    simp only [W, W', Functor.map_comp, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_inf, hl,
      Scheme.Hom.preimage_bot]
  have hsup : W ⊔ W' = ⊤ := by
    simp only [W, W', hab, Functor.map_comp, Scheme.Hom.comp_preimage, ← Scheme.Hom.preimage_sup,
      hl', Scheme.Hom.preimage_top]
  have hW : IsClopen (W : Set (D.obj m)) := by
    refine ⟨⟨?_⟩, W.2⟩
    convert W'.2 using 1
    ext x
    have h₁ : x ∉ W ⊓ W' := by rw [hinf]; simp
    have h₂ : x ∈ W ⊔ W' := by rw [hsup]; simp
    rw [TopologicalSpace.Opens.mem_inf] at h₁
    rw [TopologicalSpace.Opens.mem_sup] at h₂
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun hx ↦ h₂.resolve_left hx, fun hx hx' ↦ (h₁ ⟨hx', hx⟩).elim⟩
  refine ⟨m, W, hW, ?_⟩
  change ((c.π.app m ⁻¹ᵁ W : c.pt.Opens) : Set c.pt) = s
  rw [show c.π.app m ⁻¹ᵁ W = c.π.app k ⁻¹ᵁ A by
    rw [← Scheme.Hom.comp_preimage, c.w], hA]
  rfl

include hc in
/-- **Locally constant functions on a limit come from a stage.** -/
theorem exists_isLocallyConstant_eq_comp_of_isLimit {M : Type*} [AddCommMonoid M]
    (f : c.pt → M) (hf : IsLocallyConstant f) :
    ∃ (i : I) (g : D.obj i → M), IsLocallyConstant g ∧ f = g ∘ c.π.app i := by
  classical
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let S := hf.range_finite.toFinset
  have hS (m : S) : IsClopen (f ⁻¹' {m.1}) := hf.isClopen_fiber m.1
  choose i W hW hWf using fun m : S ↦ exists_isClopen_preimage_eq_of_isLimit D hc (hS m)
  obtain ⟨k, fk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  replace fk : ∀ m : S, k ⟶ i m := fun m ↦ (@fk (i m) (by simp)).some
  have hW' (m : S) : IsClopen (D.map (fk m) ⁻¹' W m) := (hW m).preimage (D.map (fk m)).continuous
  let g : LocallyConstant (D.obj k) M :=
    ∑ m : S, (LocallyConstant.const (D.obj k) m.1).indicator (hW' m)
  refine ⟨k, g, g.isLocallyConstant, funext fun x ↦ ?_⟩
  have hmem (m : S) : c.π.app k x ∈ D.map (fk m) ⁻¹' W m ↔ f x = m.1 := by
    have := Set.ext_iff.1 (hWf m) x
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, c.w]
    exact this
  have hx : f x ∈ S := by simp [S]
  change f x = LocallyConstant.evalAddMonoidHom (c.π.app k x) (∑ m : S, _)
  rw [map_sum]
  simp only [LocallyConstant.evalAddMonoidHom_apply, LocallyConstant.indicator_apply_eq_if,
    hmem, LocallyConstant.coe_const, Function.const_apply]
  rw [Finset.sum_eq_single ⟨f x, hx⟩ (fun m _ hm ↦ if_neg fun h ↦ hm (Subtype.ext h.symm))
    (by simp)]
  simp

omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **A locally constant function on a stage vanishing on the limit vanishes on a later
stage.** -/
theorem exists_comp_eq_zero_of_isLimit {M : Type*} [Zero M] {i : I} (g : D.obj i → M)
    (hg : IsLocallyConstant g) (h : g ∘ c.π.app i = 0) :
    ∃ (j : I) (f : j ⟶ i), g ∘ D.map f = 0 := by
  let U : (D.obj i).Opens := ⟨{x | g x ≠ 0}, (hg.isClosed_fiber 0).isOpen_compl⟩
  have hU : IsCompact (U : Set (D.obj i)) := (hg.isOpen_fiber 0).isClosed_compl.isCompact
  obtain ⟨j, f, hf⟩ := exists_map_preimage_eq_map_preimage D c hc (U := U) (V := ⊥) hU
    isCompact_empty (by
      ext x
      simp only [Scheme.Hom.preimage_bot, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false,
        iff_false]
      exact fun hx ↦ hx (congrFun h x))
  refine ⟨j, f, funext fun y ↦ ?_⟩
  by_contra hy
  have : y ∈ D.map f ⁻¹ᵁ U := hy
  rw [hf] at this
  simp at this

end AlgebraicGeometry.Scheme
