/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Classes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-!
# Cohomology classes with module coefficients, and the point

The degreewise statements of the Poincaré duality chapter pair cohomology *classes*: a class of
degree `i` of `M ∈ D(T_ét, Λ)` is a morphism `Λ_T ⟶ M[i]`, an element of
`CategoryTheory.ShiftedHom Λ_T M i`.
For the structure morphism `a : X ⟶ s` of a scheme over `s = Spec k`, the classes of `Ra_! K` and
of `Ra_* K` in `D(s_ét, Λ)` are `H^i_c(X, K)` and `H^i(X, K)`.

For a connected `T` the endomorphisms of the unit `Λ_T` are `H^0(T, Λ) = Λ`
(`AlgebraicGeometry.Etale.coefficientAlgEquiv`), so that a pairing `C ⊗ᴸ D ⟶ Λ_T` induces
`Λ`-valued pairings of classes (`AlgebraicGeometry.Etale.shiftedHomPairing`).

Over a separably closed field `k`, `D(s_ét, Λ)` is the derived category of `Λ`-modules
(blueprint, *Derived category at the point*), and its dualizable objects are the perfect
complexes (*Perfect point complex*). The two facts about them that the chapter uses are stated
once here, and the étale statements are derived from them:

* a dualizable complex has bounded cohomology, and finite cohomology modules;
* over a field `Λ`, a perfect pairing of dualizable complexes induces perfect pairings of
  their classes in complementary degrees (*Biduality at the point*).

## Main definitions

- `AlgebraicGeometry.Etale.coefficientAlgEquiv`: `Λ ≃ End (Λ_T)` for a connected `T`.
- `AlgebraicGeometry.Etale.shiftedHomUnitEquiv`: the classes of degree `0` of `Λ_T` are `Λ`.
- `AlgebraicGeometry.Etale.shiftedHomPairing`: the `Λ`-valued pairing of classes induced by a
  pairing `C ⊗ᴸ D ⟶ Λ_T`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_algebraMap_end_unit`: `algebraMap` is a bijection
  `Λ ≃ End (Λ_T)` for a connected `T`.
- `AlgebraicGeometry.Etale.exists_subsingleton_shiftedHom_of_isDualizable`,
  `AlgebraicGeometry.Etale.finite_shiftedHom_of_isDualizable`: the classes of a
  dualizable complex at the point are bounded and finite.
- `AlgebraicGeometry.Etale.isPerfPair_shiftedHomPairing`: over a field `Λ`, a perfect
  pairing at the point is perfect on classes.

## Implementation notes

That the coefficients `Λ` form a field is the hypothesis `IsField Λ` rather than an instance
`[Field Λ]`, here and in the degreewise statements of
`WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` and
`WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup`. This way the coefficients
`ModuleCat Λ` are elaborated from `[CommRing Λ]` as in every other statement; with
`[Field Λ]` the kernel has to compare the two elaborations, which times out.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

/-- The derived category `D(T_ét, Λ)` of étale sheaves of `Λ`-modules on `T`. -/
local notation "𝐃(" T ", " Λ ")" => Etale.DerivedCategoryModule Λ T

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) [ConnectedSpace T]

/-- The endomorphisms of the constant complex `Λ_T` of a connected scheme `T` are the scalars:
`algebraMap`, `r ↦ r • 𝟙`, is a bijection from `Λ` onto `End (Λ_T) = H^0(T, Λ)`. -/
theorem bijective_algebraMap_end_unit :
    Function.Bijective (algebraMap Λ (End (𝟙_ 𝐃(T, Λ)))) :=
  -- Proof sketch: the global sections of the constant sheaf `Λ` on the étale site of `T` are
  -- the locally constant functions `T → Λ`, which are constant since `T` is connected.
  sorry

/-- The coefficient ring `Λ` is the algebra of endomorphisms of the constant complex `Λ_T` of a
connected scheme `T`, through `r ↦ r • 𝟙`
(`AlgebraicGeometry.Etale.bijective_algebraMap_end_unit`).
Through its inverse, morphisms `Λ_T ⟶ Λ_T`, such as the values of the degreewise pairings, are
read as scalars. -/
noncomputable def coefficientAlgEquiv : Λ ≃ₐ[Λ] End (𝟙_ 𝐃(T, Λ)) :=
  AlgEquiv.ofBijective (Algebra.ofId Λ _) (bijective_algebraMap_end_unit Λ T)

/-- The classes of degree `n = 0` of the unit `Λ_T` of a connected scheme `T` are the scalars:
`H^0(T, Λ) = Λ`, through `AlgebraicGeometry.Etale.coefficientAlgEquiv`. -/
noncomputable def shiftedHomUnitEquiv (n : ℤ) (h : n = 0) :
    ShiftedHom (𝟙_ _) (𝟙_ 𝐃(T, Λ)) n ≃ₗ[Λ] Λ :=
  (ShiftedHom.homLinearEquiv Λ _ _ n h).symm ≪≫ₗ (coefficientAlgEquiv Λ T).symm.toLinearEquiv

@[simp]
lemma shiftedHomUnitEquiv_apply (n : ℤ) (h : n = 0) (x : ShiftedHom (𝟙_ _) (𝟙_ 𝐃(T, Λ)) n) :
    shiftedHomUnitEquiv Λ T n h x =
      (coefficientAlgEquiv Λ T).symm (x ≫ (shiftFunctorZero' _ n h).hom.app _) :=
  rfl

@[simp]
lemma shiftedHomUnitEquiv_symm_apply (n : ℤ) (h : n = 0) (r : Λ) :
    (shiftedHomUnitEquiv Λ T n h).symm r =
      ShiftedHom.mk₀ n h (coefficientAlgEquiv Λ T r) :=
  rfl

variable {Λ T}

/-- The `Λ`-valued pairing of classes `H^i(C) × H^j(D) ⟶ Λ`, `i + j = 0`, induced by a pairing
`b : C ⊗ᴸ D ⟶ Λ_T` on a connected scheme `T`: the cup product of the classes along `b`
(`AlgebraicGeometry.Etale.shiftedHomCupProduct`), a class of degree `0` of `Λ_T`, read
as a scalar (`AlgebraicGeometry.Etale.shiftedHomUnitEquiv`). -/
noncomputable def shiftedHomPairing {C D : 𝐃(T, Λ)}
    (b : ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj C).obj D ⟶ 𝟙_ _) (i j : ℤ)
    (h : i + j = 0) :
    ShiftedHom (𝟙_ _) C i →ₗ[Λ] ShiftedHom (𝟙_ _) D j →ₗ[Λ] Λ :=
  (shiftedHomCupProduct Λ b i j 0 h).compr₂ (shiftedHomUnitEquiv Λ T 0 rfl).toLinearMap

lemma shiftedHomPairing_apply {C D : 𝐃(T, Λ)}
    (b : ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj C).obj D ⟶ 𝟙_ _) (i j : ℤ)
    (h : i + j = 0) (x : ShiftedHom (𝟙_ _) C i) (y : ShiftedHom (𝟙_ _) D j) :
    shiftedHomPairing b i j h x y = (coefficientAlgEquiv Λ T).symm
      (shiftedHomCupProduct Λ b i j 0 h x y ≫ (shiftFunctorZero' _ 0 rfl).hom.app _) :=
  rfl

section Point

variable (Λ) {k : Type u} [Field k] [IsSepClosed k]

/-- Blueprint *Perfect point complex*.

Over a separably closed field `k`, a dualizable (perfect) complex `C ∈ D(Spec k_ét, Λ)` has
bounded cohomology: its classes vanish outside a bounded range of degrees. -/
theorem exists_subsingleton_shiftedHom_of_isDualizable
    {C : 𝐃(Spec (.of k), Λ)} (hC : IsDualizable C) :
    ∃ m n : ℤ, ∀ q : ℤ, q < m ∨ n < q → Subsingleton (ShiftedHom (𝟙_ _) C q) :=
  -- Proof sketch: `D(Spec k_ét, Λ)` is the derived category of `Λ`-modules (blueprint,
  -- *Derived category at the point*), and `C` is a perfect complex of `Λ`-modules, which is
  -- quasi-isomorphic to a bounded complex of projectives.
  sorry

/-- Blueprint *Perfect point complex*.

Over a separably closed field `k`, the classes of every degree of a dualizable (perfect)
complex `C ∈ D(Spec k_ét, Λ)` over a noetherian ring `Λ` form a finite `Λ`-module. -/
theorem finite_shiftedHom_of_isDualizable [IsNoetherianRing Λ]
    {C : 𝐃(Spec (.of k), Λ)} (hC : IsDualizable C) (q : ℤ) :
    Module.Finite Λ (ShiftedHom (𝟙_ _) C q) :=
  -- Proof sketch: through *Derived category at the point*, `C` is a bounded complex of finite
  -- projective `Λ`-modules, whose cohomology modules are finite as `Λ` is noetherian.
  sorry

/-- Blueprint *Biduality at the point*.

Over a separably closed field `k` and a field `Λ` of coefficients, a perfect pairing
`b : C ⊗ᴸ D ⟶ Λ` of complexes of `D(Spec k_ét, Λ)` with `C` dualizable induces perfect pairings
of classes `H^i(C) × H^j(D) ⟶ Λ` for `i + j = 0`. -/
theorem isPerfPair_shiftedHomPairing (hΛ : IsField Λ)
    {C D : 𝐃(Spec (.of k), Λ)}
    (b : ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj D ⟶ 𝟙_ _)
    (hC : IsDualizable C) (hb : IsPerfectPairing b) (i j : ℤ) (h : i + j = 0) :
    (shiftedHomPairing b i j h).IsPerfPair :=
  -- Proof sketch: through *Derived category at the point*, `D(Spec k_ét, Λ) ≃ D(Λ)` as
  -- monoidal categories, so this is a statement about perfect complexes of `Λ`-modules. Over a
  -- field a perfect complex is the direct sum of its shifted cohomology, `D ≅ C^∨` by
  -- perfectness of `b`, and `H^j(C^∨)` is the dual of `H^{-j}(C)`.
  sorry

end Point

end Etale

end AlgebraicGeometry
