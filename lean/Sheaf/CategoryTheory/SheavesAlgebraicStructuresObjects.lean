/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Algebraic sheaves as internal algebraic objects

Source: Stacks Project, Section 00YR, quadruples before Proposition 00YV and its
sextuple description of rings; Lemmas 006J and 00W2
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-objects).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- Source: Stacks Project, Section 00YR (quadruples and sextuples), Lemmas 006J and 00W2
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-objects).

`CommGrp` uses multiplicative names for addition, zero and negation. The equations
of functors are strict inverse identities, not merely an equivalence. The `eqToIso`
components transport across the asserted equality of underlying sheaves, and the
section formulas specify the canonical operations. The inverse therefore recovers
these same section operations. `IsMonHom` expresses preservation of addition and
zero; the extra inverse equation explicitly includes negation. `IsRingHom` includes
addition, zero, multiplication and one; the extra negation equation includes the
remaining structure map. Sheaf morphisms are natural transformations throughout.

Proof:
1. Products are sectionwise: glue each component of a compatible family uniquely
   (00W2; lem-weil-pbc-presheaf-finite-limits-objectwise). The empty product is the
   singleton sheaf. The universal property is def-weil-category-product. Equality
   of natural transformations and compositions are checked on sections.
2. For an abelian sheaf use sectionwise addition, zero and negation. Restriction
   homomorphisms make these natural; sectionwise axioms give the group-object laws.
   The underlying sets form a sheaf by
   lem-weil-pbc-algebraic-sheaf-iff-underlying-sets. Homomorphisms preserve the maps.
3. Conversely evaluate the internal operations on sections: the internal equations
   give an abelian group at every object; naturality makes restrictions homomorphisms.
   Apply lem-weil-pbc-algebraic-sheaf-iff-underlying-sets again. A structure-preserving
   natural transformation becomes a family of homomorphisms.
4. The constructions recover the exact same sections, restrictions and operations
   on objects, and the exact same maps on morphisms. They are strict inverse functors
   commuting with forgetting. This also proves the stated morphism criterion.
5. For rings repeat steps 2--4 with multiplication and one. Naturality makes
   restrictions ring homomorphisms; associativity, commutativity, unit and
   distributivity hold sectionwise if and only if they hold as sheaf-map equations.
   Ring homomorphisms preserve zero and negation as well as addition, multiplication
   and one (00YR, proof of 00YV, rings as sextuples). -/
theorem sheaves_algebraicStructures_objects
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    Nonempty (HasFiniteProducts (Sheaf J (Type (max u v w)))) ∧
    (∀ (F G : Sheaf J (Type (max u v w))) (U : Cᵒᵖ),
      (F ⊗ G).obj.obj U = (F.obj.obj U × G.obj.obj U)) ∧
    (∀ U : Cᵒᵖ,
      Subsingleton ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U) ∧
      Nonempty ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U)) ∧
    (∃ (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
        (G : CommGrp (Sheaf J (Type (max u v w))) ⥤ Sheaf J AddCommGrpCat.{max u v w})
        (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w})),
      G ⋙ sheafCompose J (forget AddCommGrpCat.{max u v w}) = CommGrp.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J AddCommGrpCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommGrp (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a))) ∧
      (∀ (A B : Sheaf J AddCommGrpCat.{max u v w})
          (α : (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget AddCommGrpCat.{max u v w})).map f = α) ↔
          IsMonHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          GrpObj.inv (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              GrpObj.inv (X := (F.obj B).X))) ∧
    (∃ (F : Sheaf J CommRingCat.{max u v w} ⥤ CommRingObjCat (Sheaf J (Type (max u v w))))
        (G : CommRingObjCat (Sheaf J (Type (max u v w))) ⥤ Sheaf J CommRingCat.{max u v w})
        (hF : F ⋙ CommRingObjCat.forget _ = sheafCompose J (forget CommRingCat.{max u v w})),
      G ⋙ sheafCompose J (forget CommRingCat.{max u v w}) = CommRingObjCat.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J CommRingCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommRingObjCat (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.zero (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddGrpObj.neg (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)) ∧
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) *
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (1 : A.obj.obj U))) ∧
      (∀ (A B : Sheaf J CommRingCat.{max u v w})
          (α : (sheafCompose J (forget CommRingCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget CommRingCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget CommRingCat.{max u v w})).map f = α) ↔
          IsRingHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          AddGrpObj.neg (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              AddGrpObj.neg (X := (F.obj B).X))) := by
  sorry

end CategoryTheory
