/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Constructible

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a topologically
noetherian scheme, `R` a commutative ring object of `Sheaf (Scheme.ProEt.topology X) A` and
`φ : Λ →+* Γ R` a ring homomorphism. The derived category of sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible φ` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible φ`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructible φ`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` and `φ : 𝒪_E ⟶ Γ(X, 𝒪_{E,X})` this
is `D_cons(X_proét, 𝒪_E)`; for `R = E_X` and `φ : E ⟶ Γ(X, E_X)` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Sorried input

The bounded constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`). This rests on the fact that constructible
sheaves are closed under kernels, cokernels and extensions, which is not formalized; the
instance is `sorry`ed. The derived category itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe w u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [∀ {Z Y : Scheme.{u}} (g : Z ⟶ Y), (ProEtale.upperStar A g).LaxMonoidal]
  {X : Scheme.{u}}
  {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R] [IsCommMonObj R]
  {Λ : Type w} [Ring Λ] (φ : Λ →+* Γ R)

/-- The bounded constructible complexes of sheaves of `R`-modules on a topologically noetherian
scheme `X`: the complexes `K` which are bounded for the canonical t-structure and all of whose
cohomology sheaves `Hⁿ(K)` are constructible. -/
@[nolint unusedArguments]
noncomputable def boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructible R φ ((DerivedCategory.homologyFunctor _ n).obj K)

/-- A complex is bounded constructible iff its cohomology sheaves vanish outside a finite
interval `[a, b]` and are all constructible. -/
lemma mem_boundedConstructible_iff [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :
    boundedConstructible φ K ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℤ, IsConstructible R φ ((DerivedCategory.homologyFunctor _ n).obj K) := by
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
abbrev BoundedConstructible [TopologicalSpace.NoetherianSpace X] : Type _ :=
  (boundedConstructible φ).FullSubcategory

/-- The bounded constructible complexes form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible φ).IsTriangulated :=
  sorry

end AlgebraicGeometry.ProEtale
