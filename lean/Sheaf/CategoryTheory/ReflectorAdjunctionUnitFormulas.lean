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
  classical
  -- These hypotheses describe the reflective setting; only the target reflection
  -- is needed to construct the restricted Hom equivalence.
  have _ := hCA
  have _ := hκA
  have _ := hlocalA
  have _ := hlocalB
  let P := Ac.ι ⋙ Bc.lift (L ⋙ CB) (fun X ↦ hCB (L.obj X))
  let D := Ac.lift (Bc.ι ⋙ R) (fun Y ↦ hR Y.obj Y.property)
  have hP : Functor.Linear A P := ⟨fun f r ↦ by
    ext
    exact (L ⋙ CB).map_smul r f.hom⟩
  have hD : Functor.Linear A D := ⟨fun f r ↦ by
    ext
    exact R.map_smul r f.hom⟩
  refine ⟨inferInstance, hP, inferInstance, hD, ?_⟩
  let q (M : Ac.FullSubcategory) (N : Bc.FullSubcategory) :
      (P.obj M ⟶ N) ≃ (L.obj M.obj ⟶ N.obj) :=
    InducedCategory.homEquiv.trans
      (Equiv.ofBijective (fun f ↦ κB.app (L.obj M.obj) ≫ f)
        (hκB (L.obj M.obj) N.obj N.property))
  let e (M : Ac.FullSubcategory) (N : Bc.FullSubcategory) :
      (P.obj M ⟶ N) ≃ₗ[A] (M ⟶ D.obj N) :=
    { toEquiv := ((q M N).trans (adj.homEquiv M.obj N.obj)).trans
        (InducedCategory.homEquiv (X := M) (Y := D.obj N)).symm
      map_add' := fun f g ↦ by
        ext
        change adj.homEquiv M.obj N.obj (κB.app _ ≫ (f.hom + g.hom)) =
          adj.homEquiv M.obj N.obj (κB.app _ ≫ f.hom) +
            adj.homEquiv M.obj N.obj (κB.app _ ≫ g.hom)
        simp [Adjunction.homEquiv_unit, Preadditive.comp_add]
      map_smul' := fun r f ↦ by
        ext
        change adj.homEquiv M.obj N.obj (κB.app _ ≫ (r • f.hom)) =
          r • adj.homEquiv M.obj N.obj (κB.app _ ≫ f.hom)
        simp [Adjunction.homEquiv_unit] }
  have he (M : Ac.FullSubcategory) (N : Bc.FullSubcategory) (t : P.obj M ⟶ N) :
      (e M N t).hom = adj.homEquiv M.obj N.obj (κB.app (L.obj M.obj) ≫ t.hom) :=
    rfl
  have hleft {M' M : Ac.FullSubcategory} {N : Bc.FullSubcategory}
      (f : M' ⟶ M) (g : P.obj M ⟶ N) :
      e M' N (P.map f ≫ g) = f ≫ e M N g := by
    ext
    change adj.homEquiv M'.obj N.obj
        (κB.app (L.obj M'.obj) ≫ (CB.map (L.map f.hom) ≫ g.hom)) =
      f.hom ≫ adj.homEquiv M.obj N.obj (κB.app (L.obj M.obj) ≫ g.hom)
    rw [← Category.assoc, ← κB.naturality (L.map f.hom), Category.assoc]
    exact adj.homEquiv_naturality_left f.hom _
  have hright {M : Ac.FullSubcategory} {N N' : Bc.FullSubcategory}
      (f : P.obj M ⟶ N) (g : N ⟶ N') :
      e M N' (f ≫ g) = e M N f ≫ D.map g := by
    ext
    change adj.homEquiv M.obj N'.obj (κB.app (L.obj M.obj) ≫ (f.hom ≫ g.hom)) =
      adj.homEquiv M.obj N.obj (κB.app (L.obj M.obj) ≫ f.hom) ≫ R.map g.hom
    rw [← Category.assoc]
    exact adj.homEquiv_naturality_right _ _
  let core : Adjunction.CoreHomEquiv P D :=
    { homEquiv := fun M N ↦ (e M N).toEquiv
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply (e _ _).injective
        change (e _ _) ((e _ _).symm (f ≫ g)) =
          (e _ _) (P.map f ≫ (e _ _).symm g)
        rw [LinearEquiv.apply_symm_apply, hleft, LinearEquiv.apply_symm_apply]
      homEquiv_naturality_right := hright }
  let adjc := Adjunction.mkOfHomEquiv core
  have hc (M : Ac.FullSubcategory) (N : Bc.FullSubcategory) (t : P.obj M ⟶ N) :
      adjc.homEquiv M N t = e M N t := by
    change (Adjunction.mkOfHomEquiv core).homEquiv M N t = core.homEquiv M N t
    rw [Adjunction.mkOfHomEquiv_homEquiv]
  refine ⟨adjc, (fun M N ↦ ⟨e M N, fun t ↦ (hc M N t).symm⟩), ?_, ?_, ?_⟩
  · intro M N t
    rw [hc]
    exact he M N t
  · intro M
    rw [← adjc.homEquiv_id M, hc, he]
    change adj.homEquiv M.obj _ (κB.app (L.obj M.obj) ≫ 𝟙 _) = _
    rw [Category.comp_id, adj.homEquiv_unit]
  · intro N
    apply (adj.homEquiv (R.obj N.obj) N.obj).injective
    have h := (adjc.homEquiv (D.obj N) N).apply_symm_apply (𝟙 _)
    rw [adjc.homEquiv_symm_id N, hc] at h
    have h' := congrArg InducedCategory.Hom.hom h
    rw [he] at h'
    change adj.homEquiv (R.obj N.obj) N.obj
      (κB.app (L.obj (R.obj N.obj)) ≫ (adjc.counit.app N).hom) = 𝟙 _ at h'
    rw [h', Adjunction.homEquiv_unit, adj.right_triangle_components]

end CategoryTheory
