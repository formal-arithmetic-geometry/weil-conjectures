/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison

/-!

# Bounded constructible complexes on the pro-étale site

For a scheme `X` and a concrete Grothendieck abelian coefficient category `A`, this file defines
the bounded constructible objects of the derived category `D(X_proét)` of `A`-valued pro-étale
sheaves: the objects of *étale origin*, isomorphic to `D(ν^*) K'` for a bounded constructible
complex `K'` of étale sheaves, where `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` is the comparison
functor of `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`: the essential image of
  `Dᵇc(X_ét, A)` under `D(ν^*)`.
- `AlgebraicGeometry.ProEtale.DerivedCategoryBoundedConstructible`: the full subcategory
  `Dᵇc_proét(X, A)` of `D(X_proét)` cut out by this property.

## Main results

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible.bounded`: a bounded
  constructible pro-étale complex is bounded for the canonical t-structure.

## Implementation notes

In the blueprint, a bounded constructible pro-étale complex is defined intrinsically
(`def-weil-finite-torsion-constructibility`): its homology sheaves are locally constant with
finite stalks on the strata of a finite stratification. That every such complex is of étale
origin is the lemma `lem-sf-proetale-constructible-origin`, which holds only at the finite
coefficient stages `A = A_{E,n}` (it relies on Stacks 09AK, which needs Noetherian torsion
coefficients). At these stages the blueprint itself adopts the étale-origin reading
(`def-weil-pbc-proetale-modules`), and this file takes it as the definition, for any `A`. This
avoids a pro-étale notion of constructible sheaf, which is not formalised.

For `ℓ`-adic coefficients, such as the `O_E` and `E` stages, étale origin is the wrong notion:
the pro-étale constant sheaf `Ẑ_ℓ = lim ℤ/ℓⁿ` is constructible but is not `ν^*` of the étale
constant sheaf `ℤ_ℓ`. So `ProEtale.DerivedCategory.boundedConstructible` should only be used at
the finite stages.

The notation for the pro-étale category is `Dᵇc_proét(X, A)`, so that it does not clash with the
étale notation `Dᵇc(X, A)`, which is scoped in `AlgebraicGeometry`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable (X : Scheme.{u})

namespace ProEtale

/-- An object of the derived category of pro-étale sheaves is bounded constructible if it is of
étale origin: isomorphic to `D(ν^*) K'` for a bounded constructible complex `K'` of étale
sheaves.

This agrees with the intrinsic notion of the blueprint only at the finite coefficient stages
`A = A_{E,n}` (`lem-sf-proetale-constructible-origin`, `def-weil-pbc-proetale-modules`); for
`ℓ`-adic coefficients it is strictly smaller. -/
noncomputable def DerivedCategory.boundedConstructible :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  (Etale.DerivedCategory.boundedConstructible A X).map D(ν^*(X)[A])

/-- A pro-étale complex is bounded constructible exactly when it is isomorphic to `D(ν^*) K'`
for a bounded constructible étale complex `K'`. -/
lemma DerivedCategory.boundedConstructible_iff
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory.boundedConstructible A X K ↔
      ∃ K', Etale.DerivedCategory.boundedConstructible A X K' ∧
        Nonempty (D(ν^*(X)[A]).obj K' ≅ K) :=
  ObjectProperty.prop_map_iff _ _ _

variable {A X}

/-- `D(ν^*)` sends bounded constructible étale complexes to bounded constructible pro-étale
complexes. -/
lemma DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK' : Etale.DerivedCategory.boundedConstructible A X K') :
    DerivedCategory.boundedConstructible A X (D(ν^*(X)[A]).obj K') :=
  ObjectProperty.prop_map_obj _ _ hK'

variable (A X)

/-- Being bounded constructible is invariant under isomorphism. -/
instance : (DerivedCategory.boundedConstructible A X).IsClosedUnderIsomorphisms :=
  inferInstanceAs
    ((Etale.DerivedCategory.boundedConstructible A X).map _).IsClosedUnderIsomorphisms

variable {A X}

/-- A bounded constructible pro-étale complex is bounded for the canonical t-structure: `D(ν^*)`
is induced by the exact functor `ν^*`, so it preserves boundedness. -/
lemma DerivedCategory.boundedConstructible.bounded
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.boundedConstructible A X K) :
    _root_.DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  exact _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e
    ((ν^*(X)[A]).bounded_mapDerivedCategory_obj hK'.1)

variable (A X)

/-- The bounded constructible derived category `Dᵇc_proét(X, A)` of pro-étale sheaves, realized
as the full subcategory of complexes of étale origin in the derived category of pro-étale
sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible : Type _ :=
  (DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The category structure on `Dᵇc_proét(X, A)`, inherited from `D(X_proét)`. -/
noncomputable instance : Category (DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <| Category (DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion of `Dᵇc_proét(X, A)` into the derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible.ι :
    DerivedCategoryBoundedConstructible A X ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (DerivedCategory.boundedConstructible A X).ι

@[inherit_doc DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc_proét(" X ", " A ")" => ProEtale.DerivedCategoryBoundedConstructible A X

end ProEtale

end AlgebraicGeometry
