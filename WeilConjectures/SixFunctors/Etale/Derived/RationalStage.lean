/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.SixFunctors.ClosedImmersionStages

/-!
# The rational coefficient stage `Dᵇc(X, E)`

This file formalises item (iii) of blueprint proposition `sk-prop-trace-adic`, *rationalization
and coefficient-field extension*: `Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ]` has the same objects as the
integral category and morphisms `Hom_{𝒪_E}(-, -) ⊗_{𝒪_E} E`; it is idempotent complete, so that
the canonical functor to its Karoubi envelope is an equivalence; `𝒪_E`-linear triangulated
functors and natural transformations between integral categories transport to the rational ones;
every object of `Dᵇc(X, E)` is the rationalization of an integral object (a lattice), and every
morphism is `ϖ⁻ᴺ u` for an integral morphism `u`.

## Modelling choices

* The integral category `Dᵇc(X, 𝒪_E)` is the full subcategory of the category
  `D_comp(X_ét, 𝒪_E)` of derived complete objects (`DerivedCategoryDerivedCompleteIntegral`) cut
  out by `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`. Its `Hom` groups
  are those of `D_comp(X_ét, 𝒪_E)`.
* The rational category `Dᵇc(X, E)` is the full subcategory
  `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational` of the rationalization
  `D_comp(X_ét, E)` of `D_comp(X_ét, 𝒪_E)` (`DerivedCategoryDerivedCompleteRational`, the
  Verdier quotient by the objects killed by a nonzero element of `𝒪_E`), consisting of the
  objects isomorphic to the image of an object of `Dᵇc(X, 𝒪_E)`. Since the functor induced on
  rationalizations by the fully faithful inclusion `Dᵇc(X, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` is fully
  faithful (`CategoryTheory.Rationalization.full_map`,
  `CategoryTheory.Rationalization.faithful_map`), this is the rationalization
  `Dᵇc(X, 𝒪_E)[1/ϖ]` of the integral category, and its `Hom` groups are those of the
  rationalization of `D_comp(X_ét, 𝒪_E)`.
* The descent of objects to lattices is then the definition of `boundedConstructibleRational`,
  and the description of the morphisms is the general computation of the `Hom` groups of a
  rationalization (`CategoryTheory.Rationalization.tensorHomEquiv`,
  `CategoryTheory.Rationalization.exists_eq_inv_pow_smul_map`), using that `𝒪_E` is a discrete
  valuation ring (`PadicAlgCl.isDiscreteValuationRing_integers`).
* Idempotent completeness is blueprint `lem-weil-rationalization-idempotent-complete`, which
  belongs to another part of the blueprint and is only stated here
  (`AlgebraicGeometry.Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational`).
  The Karoubi envelope carries no triangulated structure in this repository, so the equivalence
  with the Karoubi envelope is stated as an equivalence of categories.

## Main results

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` : the morphisms
  of `Dᵇc(X, E)` between rationalizations of integral objects are `Hom_{𝒪_E} ⊗_{𝒪_E} E`.
- `AlgebraicGeometry.Etale.DerivedCategory.exists_iso_of_boundedConstructibleRational` : every
  object of `Dᵇc(X, E)` is the rationalization of an object of `Dᵇc(X, 𝒪_E)`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational_exists_eq_inv_pow_smul` :
  every morphism of `Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism `u`.
- `AlgebraicGeometry.Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational` :
  `Dᵇc(X, E)` is equivalent to its Karoubi envelope.
- `AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` : `𝒪_E`-linear triangulated
  functors and natural transformations transport to `E`-linear ones on rationalizations.
-/

@[expose] public section

universe w u

open CategoryTheory Limits TensorProduct

/-- In a discrete valuation ring every nonzero element divides a power of a uniformizer. -/
lemma IsDiscreteValuationRing.exists_mul_eq_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (N : ℕ) (a : R), x * a = ϖ ^ N := by
  obtain ⟨N, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  exact ⟨N, ↑v⁻¹, by rw [mul_right_comm, Units.mul_inv, one_mul]⟩

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- The ring of integers `𝒪_E` of a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` is a discrete
valuation ring. -/
instance isDiscreteValuationRing_integers : IsDiscreteValuationRing (integers l E) where
  not_a_field' := maximalIdeal_integers_ne_bot l E

/-- The universe `u + 1` copy `Shrink 𝒪_E` of the ring of integers of a finite extension `E` of
`ℚ_ℓ` inside `ℚ̄_ℓ` is a discrete valuation ring. -/
instance isDiscreteValuationRing_shrink [Small.{u + 1} E] :
    IsDiscreteValuationRing (Shrink.{u + 1} (integers l E)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (shrinkRingEquiv.{w, u} l E)

end PadicAlgCl

namespace AlgebraicGeometry

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

namespace Etale.DerivedCategory

variable (X : Scheme.{u})

/-- Blueprint `lem-weil-rationalization-idempotent-complete`: the rationalization
`Dᵇc(X, E)` of `Dᵇc(X, 𝒪_E)` is idempotent complete. -/
theorem isIdempotentComplete_boundedConstructibleRational :
    IsIdempotentComplete (boundedConstructibleRational l E X).FullSubcategory := by
  sorry

/-- Blueprint `sk-prop-trace-adic` (iii), morphisms: the morphisms of `Dᵇc(X, E)` between the
rationalizations of two objects `L`, `L'` of `Dᵇc(X, 𝒪_E)` are `Hom(L, L') ⊗_{𝒪_E} E`, through
`a ⊗ f ↦ a • f`. -/
noncomputable def boundedConstructibleRationalHomEquiv
    (L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    E ⊗[Shrink.{u + 1} (PadicAlgCl.integers l E)] (L ⟶ L') ≃ₗ[E]
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ⟶
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L') :=
  Rationalization.tensorHomEquiv _ E L L'

/-- Blueprint `sk-prop-trace-adic` (iii), morphisms: the identification of
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` sends `a ⊗ f` to
`a • f`. -/
@[simp]
lemma boundedConstructibleRationalHomEquiv_tmul
    {L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E} (a : E)
    (f : L ⟶ L') :
    boundedConstructibleRationalHomEquiv l E X L L' (a ⊗ₜ f) =
      a • (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map f :=
  Rationalization.tensorHomEquiv_tmul _ E a f

/-- Blueprint `sk-prop-trace-adic` (iii), objects: the rationalization of an object of
`Dᵇc(X, 𝒪_E)` is an object of `Dᵇc(X, E)`. -/
lemma boundedConstructibleRational_obj
    {L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (hL : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L)) :
    boundedConstructibleRational l E X
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L) :=
  ⟨L, hL, ⟨Iso.refl _⟩⟩

/-- Blueprint `sk-prop-trace-adic` (iii), descent of objects: every object of `Dᵇc(X, E)` is the
rationalization of an object of `Dᵇc(X, 𝒪_E)` (a lattice). -/
theorem exists_iso_of_boundedConstructibleRational
    (K : (boundedConstructibleRational l E X).FullSubcategory) :
    ∃ L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E,
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
      Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K.obj) :=
  K.property

/-- Blueprint `sk-prop-trace-adic` (iii), clearing denominators: for a uniformizer `ϖ` of
`𝒪_E`, every morphism `φ : K ⟶ K'` of `Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism
`u : L ⟶ L'` between lattices `L`, `L'` of `K`, `K'` in `Dᵇc(X, 𝒪_E)`. -/
theorem boundedConstructibleRational_exists_eq_inv_pow_smul
    {ϖ : Shrink.{u + 1} (PadicAlgCl.integers l E)} (hϖ : Irreducible ϖ)
    {K K' : (boundedConstructibleRational l E X).FullSubcategory} (φ : K ⟶ K') :
    ∃ (L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E)
      (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K.obj)
      (e' : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L' ≅ K'.obj)
      (N : ℕ) (u : L ⟶ L'),
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L') ∧
      φ.hom = e.inv ≫ ((algebraMap _ E ϖ)⁻¹ ^ N •
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map u) ≫ e'.hom := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.property
  obtain ⟨L', hL', ⟨e'⟩⟩ := K'.property
  obtain ⟨N, u, h⟩ := Rationalization.exists_eq_inv_pow_smul_map E
    (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    (fun m hm ↦ IsDiscreteValuationRing.exists_mul_eq_pow (nonZeroDivisors.ne_zero hm) hϖ)
    (e.hom ≫ φ.hom ≫ e'.inv)
  refine ⟨L, L', e, e', N, u, hL, hL', ?_⟩
  rw [← h]
  simp

/-- Blueprint `sk-prop-trace-adic` (iii), idempotent completeness: `Dᵇc(X, E)` is idempotent
complete (blueprint `lem-weil-rationalization-idempotent-complete`), so that the canonical
functor to its Karoubi envelope
`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleRational` is an equivalence. -/
theorem isEquivalence_toKaroubi_boundedConstructibleRational :
    (Idempotents.toKaroubi (boundedConstructibleRational l E X).FullSubcategory).IsEquivalence :=
  have := isIdempotentComplete_boundedConstructibleRational l E X
  Rationalization.isEquivalence_toKaroubi _

/-- Blueprint `sk-prop-trace-adic` (iii), transport of functors and natural transformations:
an `𝒪_E`-linear triangulated functor `F` between derived complete integral categories induces an
`E`-linear functor `Rationalization.map _ F` between the rational categories, and a natural
transformation `τ : F ⟶ G` induces a natural transformation between the induced functors,
compatible with `τ` on rationalizations of integral objects. -/
theorem rationalization_transport {Y : Scheme.{u}}
    {F G : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E}
    [F.CommShift ℤ] [F.IsTriangulated] [F.Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))]
    [G.CommShift ℤ] [G.IsTriangulated] [G.Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))]
    (τ : F ⟶ G) :
    (Rationalization.map (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) F).Linear E ∧
      ∃ τ' : Rationalization.map (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) F ⟶
          Rationalization.map (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) G,
        ∀ L, (Rationalization.mapFac
            (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) F).inv.app L ≫
          τ'.app ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L) ≫
            (Rationalization.mapFac
              (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))) G).hom.app L =
          (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map (τ.app L) :=
  ⟨inferInstance, Rationalization.mapNatTrans _ τ, Rationalization.mapNatTrans_app _ τ⟩

end Etale.DerivedCategory

end AlgebraicGeometry
