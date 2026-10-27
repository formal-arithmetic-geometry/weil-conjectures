module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Affine refinement of a marked finite-over-smooth diagram

Source: literature/stacks-project/more-morphisms.tex, Tag 057L,
lemma-local-local-structure-finite-type-affine, proof.
(blueprint: lem-trf-marked-finite-smooth-affine-refinement)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-over-smooth diagram admits affine open neighbourhoods of its marked
points, with a surjective smooth middle map and the same singleton finite fibre.
The canonical residue-field isomorphisms commute with both residue-field maps.

Source: literature/stacks-project/more-morphisms.tex, Tag 057L,
lemma-local-local-structure-finite-type-affine, proof.
(blueprint: lem-trf-marked-finite-smooth-affine-refinement)

Proof:
1. By lem-weil-pbc-affine-opens-basis choose affine opens U₀ about s₁ and
   Y₀ about y₁ inside h₁⁻¹(U₀).
2. By lem-pc-smooth-flat and lem-weil-pbc-flat-lfp-open, h₁ is open. Choose
   an affine neighbourhood U of s₁ inside h₁(Y₀), again using the affine basis.
3. Set Y = Y₀ ∩ h₁⁻¹(U). The factorization through an open subscheme and
   lem-weil-pbc-open-preimage-fibre-product identify Y with Y₀ ×[U₀] U.
   By lem-weil-pbc-fibre-product-affine-spectra, Y is affine. The factorization
   gives the restricted map h and its commuting identity.
4. Every point of U has a preimage in Y₀; that preimage belongs to Y. Thus h
   is surjective, by def-weil-surjective-morphism.
5. The relative-dimension version of lem-weil-pbc-smooth-restrict-open-subschemes
   follows from Zariski locality of SmoothOfRelativeDimension n, as formalized
   by IsZariskiLocalAtSource.resLE. Apply it directly to h₁ to retain dimension n.
6. For every field-valued point Spec K → U, base change of the surjective h
   is nonempty by lem-weil-pbc-surjective-base-change. The commuting restriction
   square gives an open immersion into the corresponding base change of h₁,
   by lem-weil-pbc-open-fibre-product. An arbitrary chosen pullback is identified
   with the canonical pullback by its universal property, def-pc-fibre-product.
7. The ambient base change is integral by the geometric-integrality hypothesis.
   Every nonempty open subscheme of an integral scheme is integral, since its
   nonempty opens have the same section rings as their images in the ambient
   scheme. This gives the universal condition defining geometric integrality.
8. By lem-weil-pbc-open-preimage-fibre-product, W = π₁⁻¹(Y) is the canonical
   pullback open, with its restricted map π. By parts (a) and (b) of
   lem-weil-pbc-finite-morphism-permanence it is finite over Y and affine.
   The original singleton fibre restricts to precisely the marked point of W.
9. The open inclusions retain the marked points and the same stalks, maximal
   ideals and residue fields. The restriction identities identify the stalk maps;
   quotienting them gives the two displayed commuting residue-field squares.
   This uses def-weil-open-immersion and def-weil-residue-field.
-/
theorem exists_marked_finite_smooth_affine_refinement
    {W₁ V S₁ : Scheme.{u}} (n : ℕ) (π₁ : W₁ ⟶ V) (h₁ : V ⟶ S₁)
    [IsFinite π₁] [SmoothOfRelativeDimension n h₁] [GeometricallyIntegral h₁]
    (w₁ : W₁) (hπ : π₁ ⁻¹' ({π₁ w₁} : Set V) = ({w₁} : Set W₁)) :
    ∃ (U : S₁.Opens) (Y : V.Opens) (e : Y ≤ h₁ ⁻¹ᵁ U) (hy : π₁ w₁ ∈ Y),
      IsAffineOpen U ∧ IsAffineOpen Y ∧
      Surjective (h₁.resLE U Y e) ∧
      SmoothOfRelativeDimension n (h₁.resLE U Y e) ∧
      GeometricallyIntegral (h₁.resLE U Y e) ∧
      IsAffine (π₁ ⁻¹ᵁ Y).toScheme ∧ IsFinite (π₁ ∣_ Y) ∧
      (π₁ ∣_ Y) ⁻¹' ({⟨π₁ w₁, hy⟩} : Set Y) =
        ({⟨w₁, hy⟩} : Set (π₁ ⁻¹ᵁ Y)) ∧
      (π₁ ∣_ Y) ⟨w₁, hy⟩ = ⟨π₁ w₁, hy⟩ ∧
      h₁.resLE U Y e ⟨π₁ w₁, hy⟩ = ⟨h₁ (π₁ w₁), e hy⟩ ∧
      IsIso ((π₁ ⁻¹ᵁ Y).ι.residueFieldMap ⟨w₁, hy⟩) ∧
      IsIso (Y.ι.residueFieldMap ⟨π₁ w₁, hy⟩) ∧
      IsIso (U.ι.residueFieldMap ⟨h₁ (π₁ w₁), e hy⟩) ∧
      h₁.resLE U Y e ≫ U.ι = Y.ι ≫ h₁ ∧
      (π₁ ∣_ Y) ≫ Y.ι = (π₁ ⁻¹ᵁ Y).ι ≫ π₁ ∧
      (V.residueFieldCongr (morphismRestrict_base_coe π₁ Y ⟨w₁, hy⟩)).hom ≫
          π₁.residueFieldMap w₁ ≫ (π₁ ⁻¹ᵁ Y).ι.residueFieldMap ⟨w₁, hy⟩ =
        Y.ι.residueFieldMap ((π₁ ∣_ Y) ⟨w₁, hy⟩) ≫
          (π₁ ∣_ Y).residueFieldMap ⟨w₁, hy⟩ ∧
      (S₁.residueFieldCongr (h₁.coe_resLE_apply e ⟨π₁ w₁, hy⟩)).hom ≫
          h₁.residueFieldMap (π₁ w₁) ≫ Y.ι.residueFieldMap ⟨π₁ w₁, hy⟩ =
        U.ι.residueFieldMap (h₁.resLE U Y e ⟨π₁ w₁, hy⟩) ≫
          (h₁.resLE U Y e).residueFieldMap ⟨π₁ w₁, hy⟩ := by
  have : Smooth h₁ := SmoothOfRelativeDimension.smooth n h₁
  obtain ⟨U₀, hU₀, hs₀, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S₁) (x := h₁ (π₁ w₁)) (U := ⊤) (by trivial)
  obtain ⟨Y₀, hY₀, hy₀, e₀⟩ := exists_isAffineOpen_mem_and_subset
    (X := V) (x := π₁ w₁) (U := h₁ ⁻¹ᵁ U₀) hs₀
  let O : S₁.Opens := ⟨h₁ '' (Y₀ : Set V), h₁.isOpenMap _ Y₀.isOpen⟩
  obtain ⟨U, hU, hs, hUO⟩ := exists_isAffineOpen_mem_and_subset
    (X := S₁) (x := h₁ (π₁ w₁)) (U := O) ⟨π₁ w₁, hy₀, rfl⟩
  have hUU₀ : U ≤ U₀ := by
    rintro s hs
    obtain ⟨y, hy, rfl⟩ := hUO hs
    exact e₀ hy
  let Y : V.Opens := Y₀ ⊓ h₁ ⁻¹ᵁ U
  have e : Y ≤ h₁ ⁻¹ᵁ U := inf_le_right
  have hy : π₁ w₁ ∈ Y := ⟨hy₀, hs⟩
  have hY : IsAffineOpen Y := by
    have : IsAffine Y₀.toScheme := hY₀
    have : IsAffine U₀.toScheme := hU₀
    let f₀ := h₁.resLE U₀ Y₀ e₀
    have hA := (hU.preimage_of_isOpenImmersion U₀.ι (by simpa using hUU₀)).preimage f₀
    have hB := hA.image_of_isOpenImmersion Y₀.ι
    convert hB using 1
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [Y]
  let g := h₁.resLE U Y e
  have hg : Surjective g := by
    constructor
    rintro ⟨s, hs⟩
    obtain ⟨y, hy₀, hys⟩ := hUO hs
    refine ⟨⟨y, hy₀, by change h₁ y ∈ U; rwa [hys]⟩, ?_⟩
    apply Subtype.ext
    exact (h₁.coe_resLE_apply e _).trans hys
  have hdim : SmoothOfRelativeDimension n g :=
    IsZariskiLocalAtSource.resLE e inferInstance
  have hgeom : GeometricallyIntegral g := by
    constructor
    intro K _ x Z fst snd H
    let i : pullback g x ⟶ pullback h₁ (x ≫ U.ι) :=
      pullback.map _ _ _ _ Y.ι (𝟙 _) U.ι (h₁.resLE_comp_ι e) (by simp)
    have : IsOpenImmersion i := Scheme.pullback_map_isOpenImmersion ..
    have : Surjective (pullback.snd g x) := inferInstance
    have : Nonempty ↥(pullback g x) :=
      (pullback.snd g x).surjective.nonempty
    have : Nonempty Z := Nonempty.map H.isoPullback.inv inferInstance
    have : IsIntegral (pullback h₁ (x ≫ U.ι)) :=
      GeometricallyIntegral.geometrically_isIntegral (f := h₁) _ _ _ (.of_hasPullback _ _)
    exact isIntegral_of_isOpenImmersion (H.isoPullback.hom ≫ i)
  refine ⟨U, Y, e, hy, hU, hY, hg, hdim, hgeom, hY.preimage π₁,
    inferInstance, ?_, ?_, ?_, inferInstance, inferInstance, inferInstance,
    h₁.resLE_comp_ι e, morphismRestrict_ι π₁ Y, ?_, ?_⟩
  · ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      have hx' : π₁ x.val = π₁ w₁ := by
        simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx
      have : x.val ∈ π₁ ⁻¹' ({π₁ w₁} : Set V) := hx'
      rw [hπ] at this
      exact this
    · rintro rfl
      exact Subtype.ext (morphismRestrict_base_coe π₁ Y _)
  · exact Subtype.ext (morphismRestrict_base_coe π₁ Y _)
  · exact Subtype.ext (h₁.coe_resLE_apply e _)
  · have H := Scheme.Hom.residueFieldMap_congr (morphismRestrict_ι π₁ Y) ⟨w₁, hy⟩
    simpa only [Scheme.residueFieldMap_comp, Scheme.Hom.comp_apply,
      Scheme.Opens.ι_apply, Category.assoc] using H.symm
  · have H := Scheme.Hom.residueFieldMap_congr (h₁.resLE_comp_ι e) ⟨π₁ w₁, hy⟩
    simpa only [Scheme.residueFieldMap_comp, Scheme.Hom.comp_apply,
      Scheme.Opens.ι_apply, Category.assoc] using H.symm

end AlgebraicGeometry
