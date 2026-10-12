/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.FinCategory.Basic

/-! # Finite diagrams and Hom descent for filtered category colimits -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph and its
finite-diagram remark, with Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-category-descent).

Proof: The object and arrow cocones are colimits of sets. Represent any finite
lists by stage elements and take a common stage using filteredness. For each
source, target, composition and identity relation holding in the colimit, the
equality criterion for filtered colimits of sets supplies a further stage where
it holds. There are only finitely many indices and relations, so another common
refinement makes all relations hold simultaneously. The same argument applied to
two finite lists proves eventual equality of the lists of representatives.

For a functor from a finite category, enumerate all objects and all arrows. Apply
the finite lifting assertion with their endpoint relations and all identity and
composition relations. The lifted lists define a functor, since these are exactly
its functor laws. Equality with the original functor follows from its object and
arrow images, including the endpoint transports.

For an arrow between the images of X,Y at j, choose an arrow representative.
Take a common stage receiving j and its representative stage. The endpoint
identities in the object colimit become literal at a further stage; transport the
representative along these endpoint equalities. This gives the required Hom
representative. If two Hom representatives have the same image, equality in the
arrow colimit gives a common refinement where their entire arrows agree. Equalize
the resulting parallel maps out of j at one further stage by filteredness. This
proves the forward equality criterion with commuting maps out of j. Conversely,
commuting refinements and equality of stage arrows give equal images by functor
compatibility. The argument also applies to empty lists and to the empty finite
category: filteredness supplies a stage even when no representatives are needed. -/
theorem filteredColimit_category_descent
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
                Arrow.mk ((F.map i).toFunctor.map b))) := by
  sorry

end CategoryTheory
