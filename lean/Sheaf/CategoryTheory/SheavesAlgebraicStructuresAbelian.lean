module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Ring.Limits

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Intermediate algebraic-object equivalence component.
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-abelian-component)
Source: Stacks Project Section 00YR, quadruple description and Proposition 00YV.
The construction of sectionwise abelian-group objects and its inverse, including
the morphism criterion, is proved by evaluating structure maps on sections and
using the sheaf condition for underlying sets. -/
theorem sheavesAlgebraicStructuresAbelian
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
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
              GrpObj.inv (X := (F.obj B).X))) := by
  sorry

end CategoryTheory
