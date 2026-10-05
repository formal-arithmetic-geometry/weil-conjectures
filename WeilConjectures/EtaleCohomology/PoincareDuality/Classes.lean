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
degree `i` of `M ∈ D(T_ét, Λ)` is a morphism `Λ_T ⟶ M[i]`
(`AlgebraicGeometry.Etale.DerivedCategory.cohomologyClasses`, an abbreviation of
`CategoryTheory.cohomologyClasses`).
For the structure morphism `a : X ⟶ s` of a scheme over `s = Spec k`, the classes of `Ra_! K` and
of `Ra_* K` in `D(s_ét, Λ)` are `H^i_c(X, K)` and `H^i(X, K)`.

For a connected `T` the endomorphisms of the unit `Λ_T` are `H^0(T, Λ) = Λ`
(`AlgebraicGeometry.Etale.coefficientAlgEquiv`), so that a pairing `C ⊗ᴸ D ⟶ Λ_T` induces
`Λ`-valued pairings of classes (`AlgebraicGeometry.Etale.cohomologyClassesPairing`).

Over a separably closed field `k`, `D(s_ét, Λ)` is the derived category of `Λ`-modules
(blueprint, *Derived category at the point*), and its dualizable objects are the perfect
complexes (*Perfect point complex*). The two facts about them that the chapter uses are stated
once here, and the étale statements are derived from them:

* a dualizable complex has bounded cohomology, and finite cohomology modules;
* over a field `Λ`, a perfect pairing of dualizable complexes induces perfect pairings of
  their classes in complementary degrees (*Biduality at the point*).

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.cohomologyClasses`: the classes `Λ_T ⟶ M[i]`.
- `AlgebraicGeometry.Etale.coefficientAlgEquiv`, `AlgebraicGeometry.Etale.coefficientRingEquiv`:
  `Λ ≃ End (Λ_T)` for a connected `T`, as algebras and as rings.
- `AlgebraicGeometry.Etale.cohomologyClassesUnitEquiv`: the classes of degree `0` of `Λ_T` are
  `Λ`.
- `AlgebraicGeometry.Etale.cohomologyClassesPairing`: the `Λ`-valued pairing of classes
  induced by a pairing `C ⊗ᴸ D ⟶ Λ_T`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_smul_id_unit`: `r ↦ r • 𝟙` is a bijection
  `Λ ≃ End (Λ_T)` for a connected `T`.
- `AlgebraicGeometry.Etale.exists_subsingleton_cohomologyClasses_of_isDualizable`,
  `AlgebraicGeometry.Etale.finite_cohomologyClasses_of_isDualizable`: the classes of a
  dualizable complex at the point are bounded and finite.
- `AlgebraicGeometry.Etale.isPerfPair_cohomologyClassesPairing`: over a field `Λ`, a perfect
  pairing at the point is perfect on classes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

/-- The derived category `D(T_ét, Λ)` of étale sheaves of `Λ`-modules on `T`. -/
local notation "𝐃(" T ", " Λ ")" => Etale.DerivedCategoryModule Λ T

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] in
/-- The classes of degree `i` of `M ∈ D(T_ét, Λ)`, the morphisms `Λ_T ⟶ M[i]`: the general
`CategoryTheory.cohomologyClasses` in `D(T_ét, Λ)`. For the structure morphism `a` of a
scheme over `Spec k`, the classes of `Ra_! K` and `Ra_* K` are `H^i_c(X, K)` and `H^i(X, K)`. -/
abbrev DerivedCategory.cohomologyClasses {T : Scheme.{u}} (M : 𝐃(T, Λ)) (i : ℤ) :=
  CategoryTheory.cohomologyClasses M i

variable (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) [ConnectedSpace T]

/-- The endomorphisms of the constant complex `Λ_T` of a connected scheme `T` are the scalars:
`r ↦ r • 𝟙` is a bijection from `Λ` onto `End (Λ_T) = H^0(T, Λ)`. The global sections of the
constant sheaf `Λ` on the étale site of `T` are the locally constant functions `T → Λ`, which
are constant since `T` is connected. -/
theorem bijective_smul_id_unit :
    Function.Bijective (fun r : Λ ↦ r • 𝟙 (𝟙_ 𝐃(T, Λ))) :=
  sorry

/-- The coefficient ring `Λ` is the algebra of endomorphisms of the constant complex `Λ_T` of a
connected scheme `T`, through `r ↦ r • 𝟙` (`AlgebraicGeometry.Etale.bijective_smul_id_unit`).
Through its inverse, morphisms `Λ_T ⟶ Λ_T`, such as the values of the degreewise pairings, are
read as scalars. -/
noncomputable def coefficientAlgEquiv : Λ ≃ₐ[Λ] End (𝟙_ 𝐃(T, Λ)) :=
  AlgEquiv.ofBijective (Algebra.ofId Λ _) (by
    convert bijective_smul_id_unit Λ T using 1
    ext r
    exact Algebra.algebraMap_eq_smul_one r)

/-- The coefficient ring `Λ` is the ring of endomorphisms of the constant complex `Λ_T` of a
connected scheme `T`: the ring isomorphism underlying
`AlgebraicGeometry.Etale.coefficientAlgEquiv`. -/
noncomputable def coefficientRingEquiv : Λ ≃+* End (𝟙_ 𝐃(T, Λ)) :=
  (coefficientAlgEquiv Λ T).toRingEquiv

/-- The classes of degree `n = 0` of the unit `Λ_T` of a connected scheme `T` are the scalars:
`H^0(T, Λ) = Λ`, through `AlgebraicGeometry.Etale.coefficientAlgEquiv`. -/
noncomputable def cohomologyClassesUnitEquiv (n : ℤ) (h : n = 0) :
    cohomologyClasses (𝟙_ 𝐃(T, Λ)) n ≃ₗ[Λ] Λ :=
  cohomologyClassesZeroEquiv Λ _ n h ≪≫ₗ (coefficientAlgEquiv Λ T).symm.toLinearEquiv

variable {Λ T}

/-- The `Λ`-valued pairing of classes `H^i(C) × H^j(D) ⟶ Λ`, `i + j = 0`, induced by a pairing
`b : C ⊗ᴸ D ⟶ Λ_T` on a connected scheme `T`: the cup product of the classes along `b`
(`AlgebraicGeometry.Etale.cohomologyClassesCupProduct`), a class of degree `0` of `Λ_T`, read
as a scalar (`AlgebraicGeometry.Etale.cohomologyClassesUnitEquiv`). -/
noncomputable def cohomologyClassesPairing {C D : 𝐃(T, Λ)}
    (b : ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj C).obj D ⟶ 𝟙_ _) (i j : ℤ)
    (h : i + j = 0) :
    cohomologyClasses C i →ₗ[Λ] cohomologyClasses D j →ₗ[Λ] Λ :=
  (cohomologyClassesCupProduct Λ b i j).compr₂
    (cohomologyClassesUnitEquiv Λ T (i + j) h).toLinearMap

section Point

variable (Λ) {k : Type u} [Field k] [IsSepClosed k]

/-- Blueprint *Perfect point complex*.

Over a separably closed field `k`, a dualizable (perfect) complex `C ∈ D(Spec k_ét, Λ)` over a
noetherian ring `Λ` has bounded cohomology: its classes vanish outside a bounded range of
degrees. `D(Spec k_ét, Λ)` is the derived category of `Λ`-modules, and `C` is a perfect complex
of `Λ`-modules. -/
theorem exists_subsingleton_cohomologyClasses_of_isDualizable [IsNoetherianRing Λ]
    {C : 𝐃(Spec (.of k), Λ)} (hC : IsDualizable C) :
    ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → Subsingleton (cohomologyClasses C q) :=
  sorry

/-- Blueprint *Perfect point complex*.

Over a separably closed field `k`, the classes of every degree of a dualizable (perfect)
complex `C ∈ D(Spec k_ét, Λ)` over a noetherian ring `Λ` form a finite `Λ`-module. -/
theorem finite_cohomologyClasses_of_isDualizable [IsNoetherianRing Λ]
    {C : 𝐃(Spec (.of k), Λ)} (hC : IsDualizable C) (q : ℤ) :
    Module.Finite Λ (cohomologyClasses C q) :=
  sorry

/-- Blueprint *Biduality at the point*.

Over a separably closed field `k` and a field `Λ` of coefficients, a perfect pairing
`b : C ⊗ᴸ D ⟶ Λ` of complexes of `D(Spec k_ét, Λ)` with `C` dualizable induces perfect pairings
of classes `H^i(C) × H^j(D) ⟶ Λ` for `i + j = 0`. Over a field a perfect complex is the
direct sum of its shifted cohomology, `D ≅ C^∨` by perfectness of `b`, and `H^j(C^∨)` is the
dual of `H^{-j}(C)`.

That `Λ` is a field is the hypothesis `IsField Λ` rather than an instance `[Field Λ]`, so that
the coefficients `ModuleCat Λ` are elaborated from `[CommRing Λ]` as in every other statement;
with `[Field Λ]` the kernel has to compare the two elaborations, which times out. -/
theorem isPerfPair_cohomologyClassesPairing (hΛ : IsField Λ)
    {C D : 𝐃(Spec (.of k), Λ)}
    (b : ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj D ⟶ 𝟙_ _)
    (hC : IsDualizable C) (hb : IsPerfectPairing b) (i j : ℤ) (h : i + j = 0) :
    (cohomologyClassesPairing b i j h).IsPerfPair :=
  sorry

end Point

end Etale

end AlgebraicGeometry
