/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.CoextendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars

/-!
# Change of the integral coefficient stage along a finite extension

For finite extensions `E ⊆ L` of `ℚ_ℓ` inside `ℚ̄_ℓ`, the inclusion `E → L` restricts to a ring
morphism `𝒪_E → 𝒪_L` of rings of integers (`PadicAlgCl.integersMap`). A uniformizer of `𝒪_E`
becomes a unit times a power of a uniformizer of `𝒪_L`, the ring `𝒪_L` being a discrete valuation
ring (`PadicAlgCl.exists_map_uniformizer_eq_unit_mul_pow`), so the right derived functor of
coextension of scalars along `𝒪_E → 𝒪_L` carries derived complete objects to derived complete
objects (`AlgebraicGeometry.Etale.coextendScalarsDerivedCompleteIntegral`). This is the integral
part of the transition functors `K ↦ K ⊗_E L` of the `ℚ̄_ℓ` coefficient stage (blueprint
`def-weil-algebraically-closed-coefficients`); for `𝒪_L` finite free over `𝒪_E`, coextension of
scalars agrees with `− ⊗_{𝒪_E} 𝒪_L` up to the (trivial) inverse different.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] {E L : Type w} [Field E] [Field L] [Algebra E (PadicAlgCl l)]
  [Algebra L (PadicAlgCl l)] (ι : E →+* L)
  (hι : ∀ x, algebraMap L (PadicAlgCl l) (ι x) = algebraMap E (PadicAlgCl l) x)

/-- The ring morphism `𝒪_E → 𝒪_L` restricted from an embedding `ι : E → L` over `ℚ̄_ℓ`. -/
noncomputable def integersMap : integers l E →+* integers l L where
  toFun x := ⟨ι x, by
    rw [mem_integers_iff, hι]
    exact x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

variable [Small.{u + 1} E] [Small.{u + 1} L]

/-- The ring morphism `𝒪_E → 𝒪_L` on the universe `u + 1` copies. -/
noncomputable def integersShrinkMap :
    Shrink.{u + 1} (integers l E) →+* Shrink.{u + 1} (integers l L) :=
  (shrinkRingEquiv l L).toRingHom.comp
    ((integersMap l ι hι).comp (shrinkRingEquiv l E).symm.toRingHom)

/-- The ring morphisms `𝒪_E → 𝒪_L` are functorial in the embeddings. -/
lemma integersShrinkMap_comp {L' : Type w} [Field L'] [Algebra L' (PadicAlgCl l)]
    [Small.{u + 1} L'] (ι' : L →+* L')
    (hι' : ∀ x, algebraMap L' (PadicAlgCl l) (ι' x) = algebraMap L (PadicAlgCl l) x)
    [Small.{u + 1} L] :
    integersShrinkMap.{w, u} l (ι'.comp ι) (fun x ↦ (hι' _).trans (hι x)) =
      (integersShrinkMap.{w, u} l ι' hι').comp (integersShrinkMap.{w, u} l ι hι) := by
  ext x
  simp [integersShrinkMap, integersMap, shrinkRingEquiv]

lemma integersShrinkMap_injective : Function.Injective (integersShrinkMap.{w, u} l ι hι) := by
  intro x y h
  apply (shrinkRingEquiv l E).symm.injective
  have h' := congrArg (shrinkRingEquiv l L).symm h
  simp only [integersShrinkMap, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h'
  have h'' := congrArg Subtype.val h'
  simp only [integersMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at h''
  exact Subtype.ext (ι.injective h'')

variable [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]

instance : IsLocalRing (Shrink.{u + 1} (integers l L)) :=
  (shrinkRingEquiv l L).isLocalRing

instance : IsPrincipalIdealRing (Shrink.{u + 1} (integers l L)) :=
  IsPrincipalIdealRing.of_surjective (shrinkRingEquiv l L).toRingHom
    (shrinkRingEquiv l L).surjective

omit [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L] in
lemma maximalIdeal_shrink_eq : IsLocalRing.maximalIdeal (Shrink.{u + 1} (integers l L)) =
    maximalIdealShrink.{w, u} l L :=
  (IsLocalRing.map_ringEquiv_maximalIdeal (shrinkRingEquiv l L)).symm

instance : IsDiscreteValuationRing (Shrink.{u + 1} (integers l L)) where
  not_a_field' := by
    rw [maximalIdeal_shrink_eq, maximalIdealShrink, Ne,
      Ideal.map_eq_bot_iff_of_injective (shrinkRingEquiv l L).injective]
    exact maximalIdeal_integers_ne_bot l L

/-- A uniformizer of `𝒪_E` becomes, in `𝒪_L`, a unit times a power of a uniformizer `ϖ_L`. -/
lemma exists_map_uniformizer_eq_unit_mul_pow {ϖ : Shrink.{u + 1} (integers l E)}
    (hϖ : ϖ ∈ nonZeroDivisors _) {ϖ' : Shrink.{u + 1} (integers l L)}
    (hϖ' : maximalIdealShrink.{w, u} l L = Ideal.span {ϖ'}) :
    ∃ (v : (Shrink.{u + 1} (integers l L))ˣ) (e : ℕ),
      integersShrinkMap l ι hι ϖ = v * ϖ' ^ e := by
  have hne : integersShrinkMap l ι hι ϖ ≠ 0 := fun h ↦
    nonZeroDivisors.ne_zero hϖ ((map_eq_zero_iff _ (integersShrinkMap_injective l ι hι)).1 h)
  have hϖ'0 : ϖ' ≠ 0 := by
    rintro rfl
    have := (inferInstance : IsDiscreteValuationRing (Shrink.{u + 1} (integers l L))).not_a_field'
    rw [maximalIdeal_shrink_eq, hϖ', Ideal.span_singleton_eq_bot.2 rfl] at this
    exact this rfl
  obtain ⟨e, v, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ' hϖ'0
      (by rw [maximalIdeal_shrink_eq, hϖ']))
  exact ⟨v, e, h⟩

end PadicAlgCl

namespace AlgebraicGeometry.Etale

open PadicAlgCl

variable (l : ℕ) [Fact l.Prime] {E L : Type w} [Field E] [Field L] [Algebra E (PadicAlgCl l)]
  [Algebra L (PadicAlgCl l)] (ι : E →+* L)
  (hι : ∀ x, algebraMap L (PadicAlgCl l) (ι x) = algebraMap E (PadicAlgCl l) x)
  [Small.{u + 1} E] [Small.{u + 1} L]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)] [FiniteDimensional ℚ_[l] L]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The right derived coextension of scalars along `𝒪_E → 𝒪_L` carries derived complete objects of
`D(X_ét, 𝒪_E)` to derived complete objects of `D(X_ét, 𝒪_L)`. -/
lemma derivedCompleteIntegral_rightDerivedFunctor_coextendScalars (X : Scheme.{u})
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E))))}
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l L
      ((sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1}
        (integersShrinkMap.{w, u} l ι hι))).rightDerivedFunctor.obj K) := by
  obtain ⟨ϖ, hϖ, hI⟩ := exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨ϖ', hϖ', hI'⟩ := exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l L
  obtain ⟨v, e, h⟩ := exists_map_uniformizer_eq_unit_mul_pow l ι hι hϖ hI'
  exact DerivedCategory.derivedComplete_rightDerivedFunctor_coextendScalars hϖ hϖ' hI hI' v e h hK

/-- The integral part of the transition functor `K ↦ K ⊗_E L` of the `ℚ̄_ℓ` coefficient stage:
the right derived coextension of scalars `D_comp(X_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_L)`. -/
noncomputable def coextendScalarsDerivedCompleteIntegral (X : Scheme.{u}) :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l L :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l L).lift
    ((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι ⋙
      (sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1}
        (integersShrinkMap.{w, u} l ι hι))).rightDerivedFunctor)
    (fun K ↦ derivedCompleteIntegral_rightDerivedFunctor_coextendScalars l ι hι X K.property)

end AlgebraicGeometry.Etale
