/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralIdempotentComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral

/-!
# The rational coefficient stage `Dᵇc(X, E)`

This file formalises *rationalization and coefficient-field extension*:
`Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[1/ϖ]` has the same objects as the integral category and morphisms
`Hom_{𝒪_E}(-, -) ⊗_{𝒪_E} E`; it is a triangulated subcategory of `D_comp(X_ét, E)`; for `X`
separated and of finite type over a field it is idempotent complete, so that the canonical functor
to its Karoubi envelope is an equivalence; `𝒪_E`-linear triangulated functors and natural
transformations between integral categories transport to the rational ones; every object of
`Dᵇc(X, E)` is the rationalization of an integral object (a lattice), and every morphism is `ϖ⁻ᴺ u`
for an integral morphism `u`.

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
* Idempotent completeness, for `X` separated and of finite type over a field, follows from
  Ekedahl's bounded t-structure on `Dᵇc(X, E)`, an input from the theory of `ℓ`-adic sheaves
  which is only stated here
  (`Etale.DerivedCategory.exists_tStructure_bounded_boundedConstructibleRational`);
  a triangulated category with a bounded t-structure is idempotent complete
  (`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`). The lattice lemma
  (`AlgebraicGeometry.Etale.DerivedCategory.exists_boundedConstructibleIntegral_idempotent`)
  follows by splitting an idempotent and its complement.
  The Karoubi envelope carries no triangulated structure in this repository, so the equivalence
  with the Karoubi envelope is stated as an equivalence of categories.

## Main results

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` : the morphisms
  of `Dᵇc(X, E)` between rationalizations of integral objects are `Hom_{𝒪_E} ⊗_{𝒪_E} E`.
- `AlgebraicGeometry.Etale.DerivedCategory.exists_iso_of_boundedConstructibleRational` : every
  object of `Dᵇc(X, E)` is the rationalization of an object of `Dᵇc(X, 𝒪_E)`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational_exists_eq_inv_pow_smul` :
  every morphism of `Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism `u`.
- `AlgebraicGeometry.Etale.DerivedCategory.isTriangulated_boundedConstructibleRational` :
  `Dᵇc(X, E)` is a triangulated subcategory of `D_comp(X_ét, E)`.
- `AlgebraicGeometry.Etale.DerivedCategory.isEquivalence_toKaroubi_boundedConstructibleRational` :
  `Dᵇc(X, E)` is equivalent to its Karoubi envelope.
- `AlgebraicGeometry.Etale.DerivedCategory.rationalization_transport` : `𝒪_E`-linear triangulated
  functors and natural transformations transport to `E`-linear ones on rationalizations.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Pretriangulated TensorProduct

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

/-- Morphisms: the morphisms of `Dᵇc(X, E)` between the rationalizations of two objects `L`, `L'` of
`Dᵇc(X, 𝒪_E)` are `Hom(L, L') ⊗_{𝒪_E} E`, through `a ⊗ f ↦ a • f`. -/
noncomputable def boundedConstructibleRationalHomEquiv
    (L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    E ⊗[Shrink.{u + 1} (PadicAlgCl.integers l E)] (L ⟶ L') ≃ₗ[E]
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ⟶
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L') :=
  Rationalization.tensorHomEquiv _ E L L'

/-- Morphisms: the identification of
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRationalHomEquiv` sends `a ⊗ f` to
`a • f`. -/
@[simp]
lemma boundedConstructibleRationalHomEquiv_tmul
    {L L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E} (a : E)
    (f : L ⟶ L') :
    boundedConstructibleRationalHomEquiv l E X L L' (a ⊗ₜ f) =
      a • (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map f :=
  Rationalization.tensorHomEquiv_tmul _ E a f

/-- Objects: the rationalization of an object of `Dᵇc(X, 𝒪_E)` is an object of `Dᵇc(X, E)`. -/
lemma boundedConstructibleRational_obj
    {L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (hL : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L)) :
    boundedConstructibleRational l E X
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L) :=
  ⟨L, hL, ⟨Iso.refl _⟩⟩

/-- Descent of objects: every object of `Dᵇc(X, E)` is the rationalization of an object of
`Dᵇc(X, 𝒪_E)` (a lattice). -/
theorem exists_iso_of_boundedConstructibleRational
    (K : (boundedConstructibleRational l E X).FullSubcategory) :
    ∃ L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E,
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
      Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K.obj) :=
  K.property

/-- Clearing denominators: for a uniformizer `ϖ` of `𝒪_E`, every morphism `φ : K ⟶ K'` of
`Dᵇc(X, E)` is `ϖ⁻ᴺ u` for an integral morphism `u : L ⟶ L'` between lattices `L`, `L'` of `K`, `K'`
in `Dᵇc(X, 𝒪_E)`. -/
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

/-- `Dᵇc(X, 𝒪_E)` is stable under retracts in `D(X_ét, 𝒪_E)`: derived completeness, bounded
constructibility and Tor amplitude are, and the reductions of a retract are retracts of the
reductions. -/
instance isStableUnderRetracts_boundedConstructibleIntegral :
    (boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X).IsStableUnderRetracts
    where
  of_retract {M N} e hN := by
    obtain ⟨hc, a, b, h⟩ := hN
    exact ⟨(_root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).prop_of_retract
      e hc, a, b, fun n ↦ ⟨(boundedConstructible _ X).prop_of_retract (e.map _) (h n).1,
      (torAmplitudeIn _ X a b).prop_of_retract (e.map _) (h n).2⟩⟩

/-- The lattices: the objects of `D_comp(X_ét, 𝒪_E)` lying in `Dᵇc(X, 𝒪_E)`. They form a
triangulated subcategory. -/
lemma isTriangulated_boundedConstructibleIntegral_inverseImage :
    ((boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X).inverseImage
      (DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E)).IsTriangulated := by
  obtain ⟨ϖ, hϖ, hI⟩ := PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  have : Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸ PadicAlgCl.maximalIdealShrink l E) :=
    have : Finite (PadicAlgCl.integers l E ⧸ IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) :=
      inferInstanceAs (Finite (IsLocalRing.ResidueField (PadicAlgCl.integers l E)))
    Finite.of_equiv _ (Ideal.quotientEquiv _ _ (PadicAlgCl.shrinkRingEquiv l E) rfl).toEquiv
  have := DerivedCategory.isTriangulated_boundedConstructibleIntegral_of_eq_span (X := X) hϖ hI
  infer_instance

/-- A distinguished triangle of `D_comp(X_ét, E)` whose first and third vertices are
rationalizations of lattices has a middle vertex isomorphic to the rationalization of a lattice:
the third morphism is `c • Q v` for a nonzero `c ∈ E` and an integral `v`, and the cone of `v`
is a lattice. -/
lemma boundedConstructibleRational_obj₂ (T : Triangle (DerivedCategoryDerivedCompleteRational
      X.smallEtaleTopology l E)) (hT : T ∈ distTriang _)
    (h₁ : boundedConstructibleRational l E X T.obj₁)
    (h₃ : boundedConstructibleRational l E X T.obj₃) :
    boundedConstructibleRational l E X T.obj₂ := by
  have := isTriangulated_boundedConstructibleIntegral_inverseImage l E X
  set Q := DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E
  obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨L₃, hL₃, ⟨e₃⟩⟩ := h₃
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Shrink.{u + 1} (PadicAlgCl.integers l E))
  have hϖM := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have ha : algebraMap _ E ϖ ≠ 0 := (IsLocalization.map_units E ⟨ϖ, hϖM⟩).ne_zero
  obtain ⟨N, v, hv⟩ := Rationalization.exists_eq_inv_pow_smul_map E hϖM
    (fun m hm ↦ IsDiscreteValuationRing.exists_mul_eq_pow (nonZeroDivisors.ne_zero hm) hϖ)
    (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫ (Q.commShiftIso (1 : ℤ)).inv.app L₁)
  obtain ⟨M, f, g, hM⟩ := distinguished_cocone_triangle₂ v
  have hM' : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj M) :=
    ((boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X).inverseImage
      (DerivedCategoryDerivedCompleteIntegral.ι _ l E)).ext_of_isTriangulatedClosed₂ _ hM hL₁ hL₃
  set c : E := (algebraMap _ E ϖ)⁻¹ ^ N
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
  let e₃' : Q.obj L₃ ≅ T.obj₃ :=
    { hom := c⁻¹ • e₃.hom
      inv := c • e₃.inv
      hom_inv_id := by simp [smul_smul, mul_inv_cancel₀ hc]
      inv_hom_id := by simp [smul_smul, inv_mul_cancel₀ hc] }
  have hQ : Triangle.mk (Q.map f) (Q.map g) (Q.map v ≫ (Q.commShiftIso (1 : ℤ)).hom.app L₁) ∈
      distTriang _ := Q.map_distinguished _ hM
  have hv' : Q.map v = c⁻¹ • (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫
      (Q.commShiftIso (1 : ℤ)).inv.app L₁) := by
    rw [hv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hcomm : (Q.map v ≫ (Q.commShiftIso (1 : ℤ)).hom.app L₁) ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃'.hom ≫ T.mor₃ := by
    rw [hv']
    simp only [e₃', Linear.smul_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp, e₁.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact ⟨M, hM', ⟨Triangle.π₂.mapIso (isoTriangleOfIso₁₃ _ _ hQ hT e₁ e₃' hcomm)⟩⟩

instance isClosedUnderIsomorphisms_boundedConstructibleRational :
    (boundedConstructibleRational l E X).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨L, hL, ⟨e'⟩⟩ ↦ ⟨L, hL, ⟨e' ≪≫ e⟩⟩

/-- `Dᵇc(X, E)` is a triangulated subcategory of `D_comp(X_ét, E)`: it contains `0`, it is stable
under shifts, as `Dᵇc(X, 𝒪_E)` is, and it is closed under extensions
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational_obj₂`). -/
instance isTriangulated_boundedConstructibleRational :
    (boundedConstructibleRational l E X).IsTriangulated := by
  have := isTriangulated_boundedConstructibleIntegral_inverseImage l E X
  set Q := DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E
  have : (boundedConstructibleRational l E X).ContainsZero := by
    obtain ⟨Z, hZ, hPZ⟩ := ((boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E)
      X).inverseImage (DerivedCategoryDerivedCompleteIntegral.ι _ l E)).exists_prop_of_containsZero
    exact ⟨⟨Q.obj Z, Q.map_isZero hZ, Z, hPZ, ⟨Iso.refl _⟩⟩⟩
  have : (boundedConstructibleRational l E X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K ⟨L, hL, ⟨e⟩⟩ ↦ ⟨L⟦n⟧, ((boundedConstructibleIntegral
      (PadicAlgCl.maximalIdealShrink l E) X).inverseImage
        (DerivedCategoryDerivedCompleteIntegral.ι _ l E)).le_shift n _ hL,
      ⟨(Q.commShiftIso n).app L ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩⟩
  have : (boundedConstructibleRational l E X).IsTriangulatedClosed₂ :=
    .mk' fun T hT h₁ h₃ ↦ boundedConstructibleRational_obj₂ l E X T hT h₁ h₃
  exact {}

/-- **Ekedahl's theorem** (input from the theory of `ℓ`-adic sheaves). For `X` separated and of
finite type over a field `k`, the rational stage `Dᵇc(X, E)` carries a bounded t-structure.
Ekedahl's standard t-structure, whose heart is the category of constructible `E`-sheaves, is one;
the statement only asserts that some bounded t-structure exists.

References: T. Ekedahl, *On the adic formalism*; B. Bhatt, P. Scholze, *The pro-étale topology
for schemes*, §6. The blueprint works only with the pro-étale model of `Dᵇc(X, E)` and has no node
for the étale model `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleRational`; the
comparison of the two models is not available in this repository. -/
theorem exists_tStructure_bounded_boundedConstructibleRational {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    ∃ t : Triangulated.TStructure (boundedConstructibleRational l E X).FullSubcategory,
      ∀ K, t.bounded K :=
  sorry

/-- For `X` separated and of finite type over a field, the rationalization `Dᵇc(X, E)` of
`Dᵇc(X, 𝒪_E)` is idempotent complete: it is a triangulated category with a bounded t-structure
(`AlgebraicGeometry.Etale.DerivedCategory.exists_tStructure_bounded_boundedConstructibleRational`),
and such a category is idempotent complete
(`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded`). -/
theorem isIdempotentComplete_boundedConstructibleRational {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    IsIdempotentComplete (boundedConstructibleRational l E X).FullSubcategory := by
  obtain ⟨t, ht⟩ := exists_tStructure_bounded_boundedConstructibleRational l E X aX
  exact t.isIdempotentComplete_of_bounded ht

/-- **The lattice lemma.** Let `X` be separated and of finite type over a field, `L ∈ Dᵇc(X, 𝒪_E)`
and `u : L ⟶ L` with `u ≫ u = ϖᴺ • u`, so that `ϖ⁻ᴺ u` is an idempotent of the rationalization of
`L`. Then there is another lattice `L'` of the rationalization of `L` in `Dᵇc(X, 𝒪_E)` on which this
idempotent is integral: an idempotent `ε` of `L'` corresponding to `ϖ⁻ᴺ u`.

`Dᵇc(X, E)` is idempotent complete
(`AlgebraicGeometry.Etale.DerivedCategory.isIdempotentComplete_boundedConstructibleRational`), so
`ϖ⁻ᴺ u` and its complement split, with images the rationalizations of lattices `L_A` and `L_B`;
then `L' = L_A ⊞ L_B` and `ε` is the projection onto `L_A`. -/
theorem exists_boundedConstructibleIntegral_idempotent {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    {ϖ : Shrink.{u + 1} (PadicAlgCl.integers l E)} (hϖ : Irreducible ϖ)
    {L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (hL : boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L))
    (N : ℕ) (u : L ⟶ L) (hu : u ≫ u = ϖ ^ N • u) :
    ∃ (L' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) (ε : L' ⟶ L')
      (i : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L' ≅
        (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L),
      boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L') ∧ ε ≫ ε = ε ∧
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map ε ≫ i.hom =
        i.hom ≫ ((algebraMap _ E ϖ)⁻¹ ^ N •
          (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map u) := by
  have H := isIdempotentComplete_boundedConstructibleRational l E X aX
  set Q := DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E
  have hϖM := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have ha : algebraMap _ E ϖ ≠ 0 := (IsLocalization.map_units E ⟨ϖ, hϖM⟩).ne_zero
  -- the idempotent `p = ϖ⁻ᴺ u` of the rationalization of `L` and its complement split
  let K : (boundedConstructibleRational l E X).FullSubcategory :=
    ⟨Q.obj L, boundedConstructibleRational_obj l E X hL⟩
  let p : K ⟶ K := ObjectProperty.homMk ((algebraMap _ E ϖ)⁻¹ ^ N • Q.map u)
  have hp : p ≫ p = p := by
    ext
    simp only [p, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Linear.smul_comp, Linear.comp_smul, ← Functor.map_comp, hu, Functor.map_smul,
      smul_smul]
    rw [← algebraMap_smul E (ϖ ^ N), smul_smul, map_pow, ← mul_pow, ← mul_pow,
      mul_assoc, inv_mul_cancel₀ ha, mul_one]
  obtain ⟨A, iA, eA, hA₁, hA₂⟩ := (Idempotents.isIdempotentComplete_iff_isSplit.1 H) K p hp
  have hq : (𝟙 K - p) ≫ (𝟙 K - p) = 𝟙 K - p := by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, hp]
  obtain ⟨B, iB, eB, hB₁, hB₂⟩ := (Idempotents.isIdempotentComplete_iff_isSplit.1 H) K _ hq
  -- lattices `LA`, `LB` of the image and of the complement; `LA ⊞ LB` is a lattice of `K`
  obtain ⟨LA, hLA, ⟨fA⟩⟩ := A.property
  obtain ⟨LB, hLB, ⟨fB⟩⟩ := B.property
  have hIA : iA ≫ eB = 0 := by
    have h1 : iA ≫ p = iA := by rw [← hA₂, ← Category.assoc, hA₁, Category.id_comp]
    have : iA ≫ eB = iA ≫ (eB ≫ iB) ≫ eB := by rw [Category.assoc, hB₁, Category.comp_id]
    rw [this, hB₂, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      ← Category.assoc, h1, sub_self]
  have hIB : iB ≫ eA = 0 := by
    have h1 : iB ≫ p = 0 := by
      have : iB ≫ (𝟙 K - p) = iB := by rw [← hB₂, ← Category.assoc, hB₁, Category.id_comp]
      rw [Preadditive.comp_sub, Category.comp_id] at this
      simpa using this
    have : iB ≫ eA = iB ≫ (eA ≫ iA) ≫ eA := by rw [Category.assoc, hA₁, Category.comp_id]
    rw [this, hA₂, ← Category.assoc, h1, Limits.zero_comp]
  have := isTriangulated_boundedConstructibleIntegral_inverseImage l E X
  have hL' : ((boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X).inverseImage
      (DerivedCategoryDerivedCompleteIntegral.ι _ l E)) (LA ⊞ LB) :=
    ObjectProperty.ext_of_isTriangulatedClosed₂ _ _
      (Pretriangulated.binaryBiproductTriangle_distinguished LA LB) hLA hLB
  have : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts Q
  let eK : A.obj ⊞ B.obj ≅ K.obj :=
    { hom := biprod.desc iA.hom iB.hom
      inv := biprod.lift eA.hom eB.hom
      hom_inv_id := by
        ext <;> simp [← ObjectProperty.FullSubcategory.comp_hom, hA₁, hB₁, hIA, hIB]
      inv_hom_id := by
        have hsum : eA ≫ iA + eB ≫ iB = 𝟙 K := by rw [hA₂, hB₂]; abel
        rw [biprod.lift_desc]
        exact congrArg (fun f ↦ f.hom) hsum }
  let i : Q.obj (LA ⊞ LB) ≅ Q.obj L := Q.mapBiprod LA LB ≪≫ biprod.mapIso fA fB ≪≫ eK
  refine ⟨LA ⊞ LB, biprod.fst ≫ biprod.inl, i, hL', by simp, ?_⟩
  -- the idempotent `ε` projecting onto `LA` corresponds to `p`
  have hpA : ((algebraMap _ E ϖ)⁻¹ ^ N • Q.map u) = eA.hom ≫ iA.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, hA₂]; rfl
  have hinl : Q.map (biprod.inl (X := LA) (Y := LB)) ≫
      biprod.lift (Q.map biprod.fst) (Q.map biprod.snd) = biprod.inl := by
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  have hinr : Q.map (biprod.inr (X := LA) (Y := LB)) ≫
      biprod.lift (Q.map biprod.fst) (Q.map biprod.snd) = biprod.inr := by
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  have hA₁' : iA.hom ≫ eA.hom = 𝟙 _ := congrArg (fun f ↦ f.hom) hA₁
  have hIB' : iB.hom ≫ eA.hom = 0 := congrArg (fun f ↦ f.hom) hIB
  rw [hpA, ← cancel_epi (Q.mapBiprod LA LB).inv]
  apply biprod.hom_ext'
  · dsimp only [i, eK, Iso.trans_hom, biprod.mapIso_hom]
    simp only [Functor.mapBiprod_inv, Functor.mapBiprod_hom, biprod.inl_desc_assoc,
      ← Functor.map_comp_assoc, biprod.inl_fst_assoc, Category.assoc, biprod.mapIso_hom]
    rw [reassoc_of% hinl, reassoc_of% hinl]
    simp [reassoc_of% hA₁']
  · dsimp only [i, eK, Iso.trans_hom, biprod.mapIso_hom]
    simp only [Functor.mapBiprod_inv, Functor.mapBiprod_hom, biprod.inr_desc_assoc,
      ← Functor.map_comp_assoc, biprod.inr_fst_assoc, Category.assoc, biprod.mapIso_hom]
    rw [reassoc_of% hinr]
    simp [reassoc_of% hIB']

/-- Idempotent completeness: `Dᵇc(X, E)` is idempotent complete, so that the canonical functor to
its Karoubi envelope `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleRational` is an
equivalence, for `X` separated and of finite type over a field. -/
theorem isEquivalence_toKaroubi_boundedConstructibleRational {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    (Idempotents.toKaroubi (boundedConstructibleRational l E X).FullSubcategory).IsEquivalence :=
  have := isIdempotentComplete_boundedConstructibleRational l E X aX
  Rationalization.isEquivalence_toKaroubi _

/-- Transport of functors and natural transformations: an `𝒪_E`-linear triangulated functor `F`
between derived complete integral categories induces an `E`-linear functor `Rationalization.map _ F`
between the rational categories, and a natural transformation `τ : F ⟶ G` induces a natural
transformation between the induced functors, compatible with `τ` on rationalizations of integral
objects. -/
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
  ⟨inferInstance, Rationalization.mapNatTrans _ τ, fun L ↦ by
    rw [Rationalization.mapFac_hom_naturality, Iso.inv_hom_id_app_assoc]⟩

end Etale.DerivedCategory

end AlgebraicGeometry
