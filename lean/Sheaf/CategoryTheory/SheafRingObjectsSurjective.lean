module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Surjectivity component of internal ring-object reconstruction.
(blueprint: lem-weil-pbc-sheaf-ring-objects-surjective)
Proof in words: Evaluate the internal operations on each section set. The
internal ring diagrams give commutative ring structures, and naturality gives
ring-homomorphic restrictions. The underlying set sheaf therefore carries a
sheaf of commutative rings whose transported operations agree with the given
object by `hops`; extensionality and proof irrelevance identify the resulting
object with the original one, giving a preimage under `F.obj`. -/
theorem sheafRingObjects_surjective
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
    Function.Surjective F.obj := by
  sorry

end CategoryTheory
