/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFiniteSupport
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The non-closed points of the special fibre of a product are reached by generic slices

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type whose total spaces locally embed into `𝔸ᵐ_S`, `𝔸^{m'}_S`. If the generic-slicing
step of Gabber's Künneth formula holds in chart dimension `m + m' - 1` with coefficients `Λ`
(`NearbyCyclesModel.SliceKunnethFormula`), then every point `z` of the special fibre `X_s × Y_s`
which is not closed lies in the image of a morphism `h : W ⟶ X_s × Y_s` along which the pullback
of the Künneth map `Π_{A,B}` is invertible
(`NearbyCyclesModel.exists_isIso_map_kunnethMap_of_not_isClosed`): around `z`, the coordinates of
charts of the total spaces detect closed points, so one of them sends `z` to the generic point of
the special-fibre line, and `z` comes from the special fibre of the generic slice along it
(`NearbyCyclesModel.mem_range_sliceSpecialMap`).

This is the input of the closed-point criterion
(`ProEtale.CondensedRing.isIso_of_isIso_leftDerivedUpperStar_map_of_not_isClosed`) in the proof of
Gabber's formula with torsion coefficients, as the finite-support step
(`NearbyCyclesModel.exists_finite_isIso_upperStar_map_kunnethMap_of_boundedConstructible`) is for
`ℚ̄_ℓ`-coefficients.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option maxHeartbeats 1600000 in
-- the restricted Künneth maps are large terms
/-- **The non-closed points are reached by generic slices**: under the generic-slicing step in
chart dimension `m + m' - 1` with coefficients `Λ`, every point `z` of the special fibre of the
product which is not closed is the image of a point under a morphism `h : W ⟶ X_s × Y_s` along
which the pullback of the Künneth map `Π_{A,B}` is invertible. -/
theorem exists_isIso_map_kunnethMap_of_not_isClosed [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {m m' : ℕ}
    (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → SliceKunnethFormula Λ k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hA : boundedConstructible (condensedRingObj Λ X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (hB : boundedConstructible (condensedRingObj Λ Y) B) (z : Z'.left)
    (hz : ¬ IsClosed ({z} : Set Z'.left)) :
    ∃ (W : Scheme.{u}) (h : W ⟶ Z'.left) (w : W), h w = z ∧
      IsIso (L((h)^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  have : LocallyOfFiniteType Z'.hom := MorphismProperty.of_isPullback hP.isPullback_i
    hP.locallyOfFiniteType
  have : JacobsonSpace Z'.left := LocallyOfFiniteType.jacobsonSpace Z'.hom
  have : LocallyOfFiniteType X'.hom := MorphismProperty.of_isPullback
    hM.isPullback_i hM.locallyOfFiniteType
  have : LocallyOfFiniteType Y'.hom := MorphismProperty.of_isPullback
    hN.isPullback_i hN.locallyOfFiniteType
  have : JacobsonSpace X'.left := LocallyOfFiniteType.jacobsonSpace X'.hom
  have : JacobsonSpace Y'.left := LocallyOfFiniteType.jacobsonSpace Y'.hom
  have := hM.isTraitModel.isNoetherian_total
  have := hN.isTraitModel.isNoetherian_total
  have := hP.isTraitModel.isNoetherian_total
  have := hM.locallyOfFiniteType
  have := hN.locallyOfFiniteType
  -- local charts around the images of `z` in the total spaces
  obtain ⟨V, hzV, ιV, _, cV, hcardV, hcVi, hcV⟩ := hm (φ₁.total (P.i z))
  obtain ⟨W, hzW, ιW, _, cW, hcardW, hcWi, hcW⟩ := hm' (φ₂.total (P.i z))
  have : QuasiCompact V.ι := inferInstance
  have : QuasiCompact W.ι := inferInstance
  have : QuasiCompact (productOpen φ₁ φ₂ V W).ι := inferInstance
  -- the restriction of the product to `V ×_S W`
  set U := productOpen φ₁ φ₂ V W
  set ψ₁ := φ₁.restrictOpen U V inf_le_left
  set ψ₂ := φ₂.restrictOpen U W inf_le_right
  have hMV := hM.restrictOpen V
  have hNW := hN.restrictOpen W
  have hpbU : IsPullback ψ₁.total ψ₂.total (V.ι ≫ qM) (W.ι ≫ qN) := isPullback_resLE_inf hpb V W
  have hPU := isTraitModelOver_restrictOpen_productOpen (φ₂ := φ₂) hP V W
  have heMV : (M.restrictOpen V).j ≫ V.ι ≫ eM = (M.restrictOpen V).ε := by simp [← heM]
  have heNW : (N.restrictOpen W).j ≫ W.ι ≫ eN = (N.restrictOpen W).ε := by simp [← heN]
  have hR := isKunnethRestriction_restrictOpen φ₁ φ₂ V W
  have hgenU : ψ₂.generic ≫ (N.j ⁻¹ᵁ W).ι ≫ gN = ψ₁.generic ≫ (M.j ⁻¹ᵁ V).ι ≫ gM := by
    simp [ψ₁, ψ₂, Scheme.Hom.resLE_comp_ι_assoc, hgen]
  -- the coordinates of `V ×_S W`
  let coord : ιV ⊕ ιW →
      ((P.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')) :=
    Sum.elim (fun a ↦ ψ₁.total ≫ cV ≫ AffineSpace.reindex (fun _ ↦ a) (trait k'))
      (fun a ↦ ψ₂.total ≫ cW ≫ AffineSpace.reindex (fun _ ↦ a) (trait k'))
  have hcoord : ∀ i, coord i ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' =
      ψ₁.total ≫ V.ι ≫ qM := by
    rintro (a | a)
    · simp [coord, hcV]
    · simp [coord, hcW, hpbU.w]
  -- the point `z` of the restricted special fibre
  have hzU : z ∈ P.i ⁻¹ᵁ U := ⟨hzV, hzW⟩
  let v : P.i ⁻¹ᵁ U := ⟨z, hzU⟩
  have hv : (P.i ⁻¹ᵁ U).ι v = z := rfl
  -- some coordinate sends `v` to the generic point of the special-fibre line
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsClosed {specialCoordinate hPU (coord i) (hcoord i) v} := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    refine hz ?_
    have hx : IsClosed {φ₁.restrictOpenSpecial U V inf_le_left v} := by
      refine isClosed_singleton_of_isImmersion hMV cV hcV _ fun a ↦ ?_
      have := hall (Sum.inl a)
      rwa [show specialCoordinate hPU (coord (Sum.inl a)) (hcoord (Sum.inl a)) =
          φ₁.restrictOpenSpecial U V inf_le_left ≫ specialCoordinate hMV cV hcV ≫
            AffineSpace.reindex (fun _ ↦ a) (Spec (.of k')) by
        rw [← specialCoordinate_comp_reindex hMV cV hcV]
        exact specialCoordinate_comp_hom hMV ψ₁ hPU rfl _ _, Scheme.Hom.comp_apply] at this
    have hy : IsClosed {φ₂.restrictOpenSpecial U W inf_le_right v} := by
      refine isClosed_singleton_of_isImmersion hNW cW hcW _ fun a ↦ ?_
      have := hall (Sum.inr a)
      rwa [show specialCoordinate hPU (coord (Sum.inr a)) (hcoord (Sum.inr a)) =
          φ₂.restrictOpenSpecial U W inf_le_right ≫ specialCoordinate hNW cW hcW ≫
            AffineSpace.reindex (fun _ ↦ a) (Spec (.of k')) by
        rw [← specialCoordinate_comp_reindex hNW cW hcW]
        exact specialCoordinate_comp_hom hNW ψ₂ hPU hpbU.w _ _, Scheme.Hom.comp_apply] at this
    have hx' := (M.i ⁻¹ᵁ V).ι.closedPoints_subset_preimage_closedPoints hx
    have hy' := (N.i ⁻¹ᵁ W).ι.closedPoints_subset_preimage_closedPoints hy
    have hx'' : IsClosed {f₁' ((P.i ⁻¹ᵁ U).ι v)} := by
      have h : φ₁.restrictOpenSpecial U V inf_le_left ≫ (M.i ⁻¹ᵁ V).ι = (P.i ⁻¹ᵁ U).ι ≫ f₁' :=
        Scheme.Hom.resLE_comp_ι _ _
      change IsClosed {((P.i ⁻¹ᵁ U).ι ≫ f₁') v}
      rw [← h]
      exact hx'
    have hy'' : IsClosed {f₂' ((P.i ⁻¹ᵁ U).ι v)} := by
      have h : φ₂.restrictOpenSpecial U W inf_le_right ≫ (N.i ⁻¹ᵁ W).ι = (P.i ⁻¹ᵁ U).ι ≫ f₂' :=
        Scheme.Hom.resLE_comp_ι _ _
      change IsClosed {((P.i ⁻¹ᵁ U).ι ≫ f₂') v}
      rw [← h]
      exact hy'
    exact isClosed_singleton_special hM hN hpb hP _ hx'' hy''
  have hgv := AffineSpace.isGenericPoint_of_not_isClosed hi
  obtain ⟨w, hw⟩ := mem_range_sliceSpecialMap (traitSliceCoord k')
    (transcendental_traitSliceCoord k') hPU (hcoord i) v hgv
  let r' : (P.restrictSpecialFibre U).left ⟶ Z'.left := (P.i ⁻¹ᵁ U).ι
  refine ⟨_, sliceSpecialMap (traitSliceCoord k') hPU (hcoord i) ≫ r', w, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hw]
    rfl
  -- the restricted Künneth map is invertible on the slice
  have hA' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 X) _ hA
  have hB' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 Y) _ hB
  have hslice' : IsIso (L((sliceSpecialMap (traitSliceCoord k') hPU (hcoord i))^*⟦Λ⟧).map
      (kunnethMap Λ ψ₁ ψ₂ (L((𝟙 X)^*⟦Λ⟧).obj A) (L((𝟙 Y)^*⟦Λ⟧).obj B))) := by
    rcases i with a | a
    · obtain ⟨c', hc'i, hc'⟩ := exists_isImmersion_pullback_reindex cV a
        (traitSlice (traitSliceCoord k'))
      have hlt : Nat.card {j : ιV // j ≠ a} < Nat.card ιV :=
        Finite.card_subtype_lt (x := a) (by simp)
      exact (hslice (by omega)).isIso ψ₁ ψ₂ hMV hNW hpbU hPU hgenU inferInstance
        inferInstance inferInstance
        (b := cV ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (by simp [hcV])
        (by omega) (Scheme.Hom.LocallyEmbedsInAffineSpace.of_isImmersion c' hc')
        (hm'.restrict W) heMV heNW hA' hB'
    · obtain ⟨c', hc'i, hc'⟩ := exists_isImmersion_pullback_reindex cW a
        (traitSlice (traitSliceCoord k'))
      have hlt : Nat.card {j : ιW // j ≠ a} < Nat.card ιW :=
        Finite.card_subtype_lt (x := a) (by simp)
      exact isIso_map_kunnethMap_baseChangeSpecialMap_snd hMV hNW hpbU hPU hgenU
        (b := cW ≫ AffineSpace.reindex (fun _ ↦ a) (trait k')) (by simp [hcW]) _
        (hslice (by omega)) (by omega) (hm.restrict V)
        (Scheme.Hom.LocallyEmbedsInAffineSpace.of_isImmersion c' hc') heMV heNW hA' hB'
  rw [← isIso_map_map_kunnethMap_iff_of_isKunnethRestriction _ hR] at hslice'
  have hslice'' : IsIso (L((sliceSpecialMap (traitSliceCoord k') hPU (hcoord i))^*⟦Λ⟧).map
      (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) := by
    exact_mod_proofs hslice'
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp Λ
    (sliceSpecialMap (traitSliceCoord k') hPU (hcoord i)) r') _).2 hslice''

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
