/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationMap
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The morphisms of the rationalization

Let `C` be an `R`-linear triangulated category and `M` a submonoid of `R`. The rationalization
`Rationalization M C` (the Verdier quotient by the `M`-torsion objects) has the *same objects*
as `C` up to the essentially surjective localization functor `Q`, and its morphisms are the
fractions of morphisms of `C` with denominators in `M`:

```
  Hom_{C[M⁻¹]}(Q X, Q Y)  =  Hom_C(X, Y)[M⁻¹]  =  A ⊗_R Hom_C(X, Y)
```

for any localization `A` of `R` at `M`. This is the description of the *rational category*
`D(T, E) = D(T, 𝒪_E)[1/ϖ]` of blueprint `def-weil-pbc-rational-category` as the "raw scalar
localization" `Hom(K, L) ⊗_{𝒪_E} E`: the Verdier quotient by torsion objects and the raw
localization of the `Hom` groups agree.

We also show that the rationalization only depends on the *saturation* of `M`: inverting a
uniformizer `ϖ` of a discrete valuation ring `R` is the same as inverting all its nonzero
elements (`CategoryTheory.Rationalization.W_powers_eq_W_nonZeroDivisors`), so that
`D(T, 𝒪_E)[1/ϖ]` is the category `D(T, 𝒪_E)[(𝒪_E ∖ 0)⁻¹]` used to define the `E`-linear
structure (`DerivedCategoryDerivedCompleteRational`).

## Main results

- `CategoryTheory.Rationalization.isLocalizedModule` : `Q.map : Hom(X, Y) → Hom(Q X, Q Y)` is
  the localization of the `R`-module `Hom(X, Y)` at `M`.
- `CategoryTheory.Rationalization.homEquiv` : `A ⊗[R] Hom(X, Y) ≃ₗ[A] Hom(Q X, Q Y)`.
- `CategoryTheory.Rationalization.W_eq_of_dvd` : the morphisms inverted by the
  rationalization only depend on the divisibility closure of `M`.
- `CategoryTheory.Rationalization.equivalenceOfWEq`: equal classes of inverted morphisms give
  equivalent rationalizations, compatibly with the localization functors.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Category Limits Pretriangulated TensorProduct

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]

/-- The action of the localization functor on morphisms, as an `R`-linear map. -/
noncomputable def mapLinearMap (X Y : C) :
    (X ⟶ Y) →ₗ[R] ((Q M C).obj X ⟶ (Q M C).obj Y) :=
  (Q M C).mapLinearMap R

@[simp]
lemma mapLinearMap_apply {X Y : C} (f : X ⟶ Y) : mapLinearMap M C X Y f = (Q M C).map f := rfl

/-- Blueprint `def-weil-pbc-rational-category`: the morphisms of the rationalization are the
localization at `M` of the morphisms of `C`, i.e. `Hom(Q X, Q Y) = Hom(X, Y)[M⁻¹]`. -/
instance isLocalizedModule (X Y : C) : IsLocalizedModule M (mapLinearMap M C X Y) where
  map_units m := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro φ₁ φ₂ h
      simp only [Module.algebraMap_end_apply] at h
      exact smul_left_injective (C := C) m.2 h
    · intro φ
      have := isIso_smul_id m.2 ((Q M C).obj X)
      refine ⟨inv ((m : R) • 𝟙 ((Q M C).obj X)) ≫ φ, ?_⟩
      have h₁ : (m : R) • inv ((m : R) • 𝟙 ((Q M C).obj X)) = 𝟙 _ := by
        conv_rhs => rw [← IsIso.hom_inv_id ((m : R) • 𝟙 ((Q M C).obj X))]
        rw [Linear.smul_comp, id_comp]
      rw [Module.algebraMap_end_apply, ← Linear.smul_comp, h₁, id_comp]
  surj φ := by
    obtain ⟨m, hm, f, hf⟩ := exists_smul_eq_map φ
    exact ⟨⟨f, ⟨m, hm⟩⟩, hf⟩
  exists_of_eq {f g} h := by
    obtain ⟨m, hm, h'⟩ := (map_eq_map_iff f g).1 h
    exact ⟨⟨m, hm⟩, h'⟩

variable (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]

instance (X Y : Rationalization M C) : IsScalarTower R A (X ⟶ Y) where
  smul_assoc r a f := by
    rw [Algebra.smul_def, mul_smul, algebraMap_smul]

/-- Blueprint `def-weil-pbc-rational-category`: the morphisms of the rationalization are
obtained by extending scalars from `R` to a localization `A` of `R` at `M`,
`A ⊗[R] Hom(X, Y) ≃ Hom(Q X, Q Y)`. For `R = 𝒪_E` and `A = E` this is the description
`Hom_{D(T, E)}(K, L) = Hom_{D(T, 𝒪_E)}(K, L) ⊗_{𝒪_E} E` of the rational category. -/
noncomputable def homEquiv (X Y : C) :
    A ⊗[R] (X ⟶ Y) ≃ₗ[A] ((Q M C).obj X ⟶ (Q M C).obj Y) :=
  (IsLocalizedModule.isBaseChange M A (mapLinearMap M C X Y)).equiv

@[simp]
lemma homEquiv_tmul (X Y : C) (a : A) (f : X ⟶ Y) :
    homEquiv M C A X Y (a ⊗ₜ f) = a • (Q M C).map f :=
  IsBaseChange.equiv_tmul _ _ _

section Saturation

variable {M C}

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C] in
lemma torsion_le_of_dvd {M' : Submonoid R} (h : ∀ m' ∈ M', ∃ m ∈ M, m' ∣ m) :
    torsion M' C ≤ torsion M C := by
  rintro X ⟨m', hm', hX⟩
  obtain ⟨m, hm, a, rfl⟩ := h m' hm'
  exact ⟨_, hm, by rw [mul_comm, mul_smul, hX, smul_zero]⟩

omit [IsTriangulated C] in
/-- The rationalization at `M` only depends on the divisibility closure of `M`: if every
element of `M'` divides an element of `M` and conversely, then `M` and `M'` have the same
torsion objects, hence the same inverted morphisms. -/
lemma W_eq_of_dvd {M' : Submonoid R} (h : ∀ m' ∈ M', ∃ m ∈ M, m' ∣ m)
    (h' : ∀ m ∈ M, ∃ m' ∈ M', m ∣ m') : W M C = W M' C := by
  rw [W, W, le_antisymm (torsion_le_of_dvd h') (torsion_le_of_dvd h)]

omit [IsTriangulated C] in
/-- Inverting a uniformizer `ϖ` of a discrete valuation ring is the same as inverting all its
nonzero elements. -/
lemma W_powers_eq_W_nonZeroDivisors [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) : W (Submonoid.powers ϖ) C = W (nonZeroDivisors R) C := by
  refine W_eq_of_dvd ?_ ?_
  · intro m hm
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero hm) hϖ
    exact ⟨_, ⟨n, rfl⟩, hn.dvd⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) n, dvd_rfl⟩

variable (C) {M' : Submonoid R}

lemma isLocalization_Q_of_W_eq (h : W M C = W M' C) : (Q M C).IsLocalization (W M' C) := by
  rw [← h]
  infer_instance

/-- Two submonoids with the same inverted morphisms (e.g. `W_powers_eq_W_nonZeroDivisors`) give
equivalent rationalizations. -/
noncomputable def equivalenceOfWEq (h : W M C = W M' C) :
    Rationalization M C ≌ Rationalization M' C :=
  have := isLocalization_Q_of_W_eq C h
  Localization.uniq (Q M C) (Q M' C) (W M' C)

/-- The equivalence `equivalenceOfWEq` is compatible with the localization functors. -/
noncomputable def compEquivalenceOfWEqFunctor (h : W M C = W M' C) :
    Q M C ⋙ (equivalenceOfWEq C h).functor ≅ Q M' C :=
  have := isLocalization_Q_of_W_eq C h
  Localization.compUniqFunctor (Q M C) (Q M' C) (W M' C)

end Saturation

end CategoryTheory.Rationalization
