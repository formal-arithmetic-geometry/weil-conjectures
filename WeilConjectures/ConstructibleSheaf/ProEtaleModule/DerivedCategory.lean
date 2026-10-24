/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme, `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of
sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible R` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible R`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructible R`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` this is `D_cons(X_proét, 𝒪_E)`;
for `R = E_X` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Sorried input

For the `ℓ`-adic coefficient rings `Λ_X = p_X^* Λ` with `Λ` one of `𝒪̲_E` or `E̲` for a finite
extension `E` of `ℚ_ℓ`, or `ℚ̲̄_ℓ`, the bounded constructible complexes on a topologically
noetherian scheme form a triangulated subcategory. This is stated separately for each of these
coefficient rings (`ProEtale.isTriangulated_boundedConstructible_padicIntegersRingObj`,
`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj`,
`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj`). It rests on the fact that
constructible sheaves of `Λ_X`-modules on such a scheme are closed under kernels, cokernels and
extensions (Bhatt–Scholze, Section 6.8), which is not formalized; the instances are `sorry`ed.
It is false for a general commutative ring object `R`: for `X = Spec k̄` and `R` the constant
sheaf of the non-coherent ring `k[x₁, x₂, …]/(x₁xᵢ)ᵢ`, the cone of `x₁ : R ⟶ R` has `H⁻¹` the
constant sheaf of the ideal `(x₂, x₃, …)`, which is not finitely generated. Noetherianity is
assumed only there: the definition `ProEtale.boundedConstructible` makes sense on any scheme. The
derived category itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

/-- The bounded constructible complexes of sheaves of `R`-modules on `X`: the complexes `K`
which are bounded for the canonical t-structure and all of whose cohomology sheaves `Hⁿ(K)`
are constructible. -/
noncomputable def boundedConstructible :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructible R ((DerivedCategory.homologyFunctor _ n).obj K)

omit [IsCommMonObj R] in
/-- A complex is bounded constructible iff its cohomology sheaves vanish outside a finite
interval `[a, b]` and are all constructible. -/
lemma mem_boundedConstructible_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :
    boundedConstructible R K ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℤ, IsConstructible R ((DerivedCategory.homologyFunctor _ n).obj K) := by
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i hi
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ h i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ h i (Or.inr hi)⟩⟩

/-- The bounded constructible derived category `D_cons(X_proét, R)`. -/
abbrev BoundedConstructible : Type _ :=
  (boundedConstructible R).FullSubcategory

section Triangulated

open scoped CategoryTheory.Obj

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the bounded constructible complexes of
`𝒪_{E,X}`-modules on a topologically noetherian scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).IsTriangulated :=
  sorry

-- The prime `ℓ` of `E̲` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
/-- For a finite extension `E` of `ℚ_ℓ`, the bounded constructible complexes of `E_X`-modules on a
topologically noetherian scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated :=
  sorry

/-- The bounded constructible complexes of `ℚ̄_{ℓ,X}`-modules on a topologically noetherian scheme
form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_padicAlgClRingObj :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated :=
  sorry

end Triangulated

end AlgebraicGeometry.ProEtale
