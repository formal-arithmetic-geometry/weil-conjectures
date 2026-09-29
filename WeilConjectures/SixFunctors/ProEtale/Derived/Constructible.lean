/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
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
  `Dᵇc(X, A)` of `D(X_proét)` cut out by this property.

## Main results

- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible.bounded`: a bounded
  constructible pro-étale complex is bounded for the canonical t-structure.

## Implementation notes

The blueprint (`sk-def-sf-categories`, and the proof of `sk-cor-sf-direct-image-ctf`) uses that
every bounded constructible pro-étale complex is of étale origin; here this is taken as the
definition. It avoids a pro-étale notion of constructible sheaf, which is not formalised.

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
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

variable (X : Scheme.{u})

namespace ProEtale

/-- An object of the derived category of pro-étale sheaves is bounded constructible if it is of
étale origin: isomorphic to `D(ν^*) K'` for a bounded constructible complex `K'` of étale
sheaves. -/
noncomputable def DerivedCategory.boundedConstructible :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  (Etale.DerivedCategory.boundedConstructible A X).map D(ν^*(X)[A])

omit [HasSmallSiteSheafify A] in
/-- A pro-étale complex is bounded constructible exactly when it is isomorphic to `D(ν^*) K'`
for a bounded constructible étale complex `K'`. -/
lemma DerivedCategory.boundedConstructible_iff
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory.boundedConstructible A X K ↔
      ∃ K', Etale.DerivedCategory.boundedConstructible A X K' ∧
        Nonempty (D(ν^*(X)[A]).obj K' ≅ K) := by
  simp [DerivedCategory.boundedConstructible, ObjectProperty.map]

variable {A X}

omit [HasSmallSiteSheafify A] in
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

omit [HasSmallSiteSheafify A] in
/-- A bounded constructible pro-étale complex is bounded for the canonical t-structure: `D(ν^*)`
commutes with homology, so it preserves homology vanishing outside an interval. -/
lemma DerivedCategory.boundedConstructible.bounded
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.boundedConstructible A X K) :
    _root_.DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨K', hK', ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff A X K).1 hK
  obtain ⟨a, b, ha, hb⟩ :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K').2 hK'.1
  have hzero : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K') →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K) := fun i hi ↦
    ((ν^*(X)[A]).map_isZero hi).of_iso
      (((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm ≪≫
        ((ν^*(X)[A]).mapDerivedCategoryHomologyFunctorIso i).symm.app K')
  refine (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1 ⟨a, b, ?_, ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦
      hzero i ((_root_.DerivedCategory.isGE_iff K' a).1 ha i hi)
  · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦
      hzero i ((_root_.DerivedCategory.isLE_iff K' b).1 hb i hi)

variable (A X)

/-- The bounded constructible derived category `Dᵇc(X, A)` of pro-étale sheaves, realized as the
full subcategory of complexes of étale origin in the derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible : Type _ :=
  (DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The category structure on `Dᵇc(X, A)`, inherited from `D(X_proét)`. -/
noncomputable instance : Category (DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <| Category (DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion of `Dᵇc(X, A)` into the derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible.ι :
    DerivedCategoryBoundedConstructible A X ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (DerivedCategory.boundedConstructible A X).ι

@[inherit_doc DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " A ")" => ProEtale.DerivedCategoryBoundedConstructible A X

end ProEtale

end AlgebraicGeometry
