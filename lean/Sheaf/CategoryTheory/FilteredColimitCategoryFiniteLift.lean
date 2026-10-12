/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Finite diagrams and Hom descent for filtered category colimits -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph;
Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-category-finite-lift).

Proof: Choose stage representatives of the objects and arrows using joint
surjectivity of their set colimits. Move the finitely many stages to a common
stage. For each arrow endpoint that equals a listed object in the colimit,
use eventual equality in the object colimit and refine until the equality holds.
Do the same for every pair of arrow endpoints that coincide. At this stage every
listed composite is defined. Functoriality identifies its colimit image with
the listed composite in O. Eventual equality in the arrow colimit now makes
each required composition and identity equation hold at a further stage.
There are finitely many of these equations; a common refinement preserves all
of them. The empty-list case uses the nonemptiness of the filtered category. -/
theorem filteredColimit_category_finite_lift
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∀ (_s : Category.{z} O) (V : ∀ j : J, F.obj j ⥤ O),
      ((∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f)) →
      (∀ (n m : ℕ) (X : Fin n → O) (A : Fin m → Arrow O),
        ∃ (j : J) (Xj : Fin n → F.obj j) (Aj : Fin m → Arrow (F.obj j)),
          (∀ q, (V j).obj (Xj q) = X q) ∧
          (∀ p, (V j).mapArrow.obj (Aj p) = A p) ∧
          (∀ p q, (A p).left = X q → (Aj p).left = Xj q) ∧
          (∀ p q, (A p).right = X q → (Aj p).right = Xj q) ∧
          (∀ p q r (h : (A p).right = (A q).left),
            Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
            ∃ hj : (Aj p).right = (Aj q).left,
              Arrow.mk ((Aj p).hom ≫ eqToHom hj ≫ (Aj q).hom) = Aj r) ∧
          (∀ p q, A p = Arrow.mk (𝟙 (X q)) → Aj p = Arrow.mk (𝟙 (Xj q)))) := by
  sorry

end CategoryTheory
