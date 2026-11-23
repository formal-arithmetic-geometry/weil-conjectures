/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.FinCategory.Basic
import WeilConjectures.CategoryTheory.FilteredColimitCategoryStructure
import WeilConjectures.CategoryTheory.FilteredColimitCategoryDescent
import WeilConjectures.CategoryTheory.FilteredColimitCategoryIso

/-! # Filtered colimits of categories

## References

* Stacks Project, Sites, Tag 09YL; Categories, Tag 04AX.
-/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The chosen object colimit admits the induced category structure. Its arrows are the
set colimit of the arrows at the stages.

Stacks Project, Tags 09YL and 04AX. -/
theorem exists_filteredColimit_category
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∃ (s : Category.{z} O),
    letI := s
    ∃ V : ∀ j : J, F.obj j ⥤ O,
      (∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f) ∧
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
          (∀ p q, A p = Arrow.mk (𝟙 (X q)) → Aj p = Arrow.mk (𝟙 (Xj q)))) ∧
      (∀ (n m : ℕ) (j k : J)
        (Xj : Fin n → F.obj j) (Xk : Fin n → F.obj k)
        (Aj : Fin m → Arrow (F.obj j)) (Ak : Fin m → Arrow (F.obj k)),
        (∀ q, (V j).obj (Xj q) = (V k).obj (Xk q)) →
        (∀ p, (V j).mapArrow.obj (Aj p) = (V k).mapArrow.obj (Ak p)) →
        ∃ (t : J) (f : j ⟶ t) (g : k ⟶ t),
          (∀ q, (F.map f).toFunctor.obj (Xj q) = (F.map g).toFunctor.obj (Xk q)) ∧
          (∀ p, (F.map f).toFunctor.mapArrow.obj (Aj p) =
            (F.map g).toFunctor.mapArrow.obj (Ak p))) ∧
      (∀ (D : Type z) [SmallCategory D] [FinCategory D] (d : D ⥤ O),
        ∃ (j : J) (dj : D ⥤ F.obj j), dj ⋙ V j = d) ∧
      (∀ (j : J) (X Y : F.obj j),
        (∀ b : (V j).obj X ⟶ (V j).obj Y,
          ∃ (k : J) (f : j ⟶ k)
            (g : (F.map f).toFunctor.obj X ⟶ (F.map f).toFunctor.obj Y),
            Arrow.mk ((V k).map g) = Arrow.mk b) ∧
        (∀ (k l : J) (f : j ⟶ k) (g : j ⟶ l)
          (a : (F.map f).toFunctor.obj X ⟶ (F.map f).toFunctor.obj Y)
          (b : (F.map g).toFunctor.obj X ⟶ (F.map g).toFunctor.obj Y),
          Arrow.mk ((V k).map a) = Arrow.mk ((V l).map b) ↔
          ∃ (t : J) (h : k ⟶ t) (i : l ⟶ t),
            f ≫ h = g ≫ i ∧
              Arrow.mk ((F.map h).toFunctor.map a) =
                Arrow.mk ((F.map i).toFunctor.map b))) ∧
      (∀ a : Arrow O, IsIso a.hom ↔
        ∃ (j : J) (b : Arrow (F.obj j)),
          IsIso b.hom ∧ (V j).mapArrow.obj b = a) := by
  obtain ⟨s, V, hObj, hCompat, hArrows⟩ := filteredColimit_category_structure J F
  obtain ⟨hLift, hEqual, hFinite, hHom⟩ :=
    filteredColimit_category_descent J F s V ⟨hObj, hCompat, hArrows⟩
  exact ⟨s, V, hObj, hCompat, hArrows, hLift, hEqual, hFinite, hHom,
    filteredColimit_category_iso_clause J F s V hFinite⟩

end CategoryTheory
