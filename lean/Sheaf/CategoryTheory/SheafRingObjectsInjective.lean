module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Injectivity component of internal ring-object reconstruction.
(blueprint: lem-weil-pbc-sheaf-ring-objects-injective)
Proof in words: Given equal internal objects, the underlying sheaves agree by `hF`.
The five transported sectionwise operations agree by `hops`, so addition, zero,
negation, multiplication, and one agree on every section. Ring structures,
restriction maps, and sheaf witnesses are then equal by extensionality and
proof irrelevance, yielding equality of the original sheaves of rings. -/
theorem sheafRingObjects_injective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J CommRingCat.{max u v w} ⥤
      CommRingObjCat (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommRingObjCat.forget _ =
      sheafCompose J (forget CommRingCat.{max u v w}))
    (hops : ∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
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
            (1 : A.obj.obj U))) :
    Function.Injective F.obj := by
  sorry

end CategoryTheory
