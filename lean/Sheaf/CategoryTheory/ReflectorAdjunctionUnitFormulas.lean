/-
Copyright (c) 2026 Weil Conjectures Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures Formalization Project
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-! # Restricting an adjunction through completion reflectors

Source: Stacks Project, Tag 099K, `lemma-pushforward-derived-complete-adjoint`,
final Hom bijection; abstract linear refinement and unit/counit calculation supplied
in the DAG (blueprint: lem-sbc-reflector-adjunction-unit-formulas).

The restrictions are the existing `ObjectProperty.lift` constructions. Their
adjunction is specified by precomposition with the given reflection unit, including
when that unit on the ordinary left adjoint's output is not invertible.
-/

@[expose] public section

set_option autoImplicit false

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

/-- Restriction through full additive reflective subcategories has the specified
linear Hom bijection and the ordinary-to-completed unit and counit formulas.
Source: Stacks Project, Tag 099K, final Hom bijection, with the abstract scalar and
unit/counit refinement in the DAG; Tag 0037 for the adjunction convention
(blueprint: lem-sbc-reflector-adjunction-unit-formulas).

Proof:
1. The left restriction is `Ac.ι` followed by the lift of `L ⋙ CB`; the right
   restriction is the lift of `Bc.ι ⋙ R`. They land in the stated subcategories
   by `hCB` and `hR`. Their morphism maps inherit additivity and scalar linearity
   from the ambient functors [def-weil-linear-functor].
2. For complete N, precomposition with `κB.app (L.obj M.obj)` is bijective by
   `hκB`, whether or not `L.obj M.obj` is complete. Bilinearity of composition
   [def-weil-linear-category] makes this map linear. Its inverse is linear by
   applying injectivity to the addition and scalar equations.
3. The ordinary adjunct of s is `adj.unit.app M.obj ≫ R.map s`, by
   [lem-weil-pbc-adjunction-of-natural-bijection]. It is linear by linearity of
   R and composition, and its inverse is linear by injectivity.
4. Compose these two bijections. Naturality of κB and the two naturality laws
   for the ordinary adjunction give naturality in M and N of their composite.
5. Apply `Adjunction.mkOfHomEquiv`
   [lem-weil-pbc-adjunction-of-natural-bijection]. Its Hom equivalence is the
   displayed composite; its natural unit and counit satisfy both triangles.
6. Evaluate this Hom equivalence at the identity of the left restriction's
   output. Precomposition gives κB, so the ordinary unit formula gives the
   asserted ambient completed-unit formula.
7. The completed counit is the inverse adjunct of the identity. Applying the
   ordinary inverse adjunct gives `κB ≫ εc = ε`. The general adjunct agreement
   is the defining composite Hom formula. No inverse of κB on L M is used.
-/
theorem exists_reflector_restricted_adjunction
    (A : Type w) [CommRing A]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
    [Linear A C]
    (E : Type u₂) [Category.{v₂} E] [Preadditive E] [HasFiniteBiproducts E]
    [Linear A E]
    (Ac : ObjectProperty C) (Bc : ObjectProperty E)
    [HasFiniteBiproducts Ac.FullSubcategory] [HasFiniteBiproducts Bc.FullSubcategory]
    (CA : C ⥤ C) [CA.Additive] [CA.Linear A]
    (CB : E ⥤ E) [CB.Additive] [CB.Linear A]
    (κA : 𝟭 C ⟶ CA) (κB : 𝟭 E ⟶ CB)
    (hCA : ∀ X : C, Ac (CA.obj X)) (hCB : ∀ X : E, Bc (CB.obj X))
    (hκA : ∀ (X Y : C), Ac Y →
      Function.Bijective (fun f : CA.obj X ⟶ Y => κA.app X ≫ f))
    (hκB : ∀ (X Y : E), Bc Y →
      Function.Bijective (fun f : CB.obj X ⟶ Y => κB.app X ≫ f))
    (hlocalA : ∀ X : C, Ac X ↔ IsIso (κA.app X))
    (hlocalB : ∀ X : E, Bc X ↔ IsIso (κB.app X))
    (L : C ⥤ E) [L.Additive] [L.Linear A]
    (R : E ⥤ C) [R.Additive] [R.Linear A] (adj : L ⊣ R)
    (hR : ∀ Y : E, Bc Y → Ac (R.obj Y)) :
    (Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X => hCB (L.obj X))).Additive ∧
      Functor.Linear A (Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X => hCB (L.obj X))) ∧
      (Ac.lift (Bc.ι ⋙ R) (fun Y => hR Y.obj Y.property)).Additive ∧
      Functor.Linear A (Ac.lift (Bc.ι ⋙ R) (fun Y => hR Y.obj Y.property)) ∧
      ∃ adjc :
        (Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X => hCB (L.obj X))) ⊣
          (Ac.lift (Bc.ι ⋙ R) (fun Y => hR Y.obj Y.property)),
        (∀ (M : Ac.FullSubcategory) (N : Bc.FullSubcategory),
          ∃ e :
            (((Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X => hCB (L.obj X))).obj M) ⟶ N) ≃ₗ[A]
              (M ⟶ (Ac.lift (Bc.ι ⋙ R) (fun Y => hR Y.obj Y.property)).obj N),
            ∀ t, e t = adjc.homEquiv M N t) ∧
        (∀ (M : Ac.FullSubcategory) (N : Bc.FullSubcategory)
          (t : (Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X => hCB (L.obj X))).obj M ⟶ N),
          (adjc.homEquiv M N t).hom =
            adj.homEquiv M.obj N.obj (κB.app (L.obj M.obj) ≫ t.hom)) ∧
        (∀ M : Ac.FullSubcategory,
          (adjc.unit.app M).hom = adj.unit.app M.obj ≫ R.map (κB.app (L.obj M.obj))) ∧
        (∀ N : Bc.FullSubcategory,
          κB.app (L.obj (R.obj N.obj)) ≫ (adjc.counit.app N).hom = adj.counit.app N.obj) := by
  sorry

end CategoryTheory
