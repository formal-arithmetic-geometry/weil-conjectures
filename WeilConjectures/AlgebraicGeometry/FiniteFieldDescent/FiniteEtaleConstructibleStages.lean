/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Finite field-extension stages of a scheme over a field

The base changes `Y_A` of `Y → Spec K` along field extensions `A/K`, their transitions, the
derived pullbacks between them, and the bounded constructible finite-Tor property.

Source: Stacks Project, Lemma 09YU (3)
(blueprint: lem-sfb-finite-etale-constructible-hom-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- The canonical fibre product `Y_A` at a field extension `A/K`.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
noncomputable abbrev scheme (A : Type u) [Field A] [Algebra K A] : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The canonical transition `Y_B ⟶ Y_A` induced by a `K`-algebra map `A ⟶ B`.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
noncomputable def projection {A B : Type u} [Field A] [Field B] [Algebra K A]
    [Algebra K B] (h : A →ₐ[K] B) : scheme f B ⟶ scheme f A :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom h.toRingHom)) (𝟙 _)
    (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext x
      exact (h.commutes x).symm)

/-- The derived inverse-image functor along a transition of finite stages.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
noncomputable abbrev pull (Λ : Type (u + 1)) [CommRing Λ]
    {A B : Type u} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (h : A →ₐ[K] B) :=
  (upperStar (ModuleCat.{u + 1} Λ) (projection f h)).leftDerivedFunctor

/-- The bounded constructible finite-Tor property at one finite stage.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
abbrev ctf (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [Field A] [Algebra K A]
    (P : DerivedCategoryModule Λ (scheme f A)) : Prop :=
  DerivedCategory.boundedConstructibleFiniteTor Λ (scheme f A) P

end AlgebraicGeometry.Etale.FiniteFieldDescent
