/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.Algebra.Category.Grp.Limits
import WeilConjectures.CategoryTheory.SheafAbelianObjectsSurjective
import WeilConjectures.CategoryTheory.SheafAbelianObjectsInjective

/-!
# Sectionwise abelian sheaves and commutative group objects

## References

* Stacks Project, Section 00YR and Proposition 00YV.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- A functor from abelian sheaves to internal commutative group objects in sheaves of sets,
compatible with the forgetful functors and the sectionwise operations, is bijective on objects.

Stacks Project, Section 00YR (quadruples) and Proposition 00YV. -/
theorem sheafAbelianObjects_bijective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w}))
    (hsections : (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)))) :
    Function.Bijective F.obj := by
  exact ⟨sheafAbelianObjects_injective J F hF hsections,
    sheafAbelianObjects_surjective J F hF hsections⟩

end CategoryTheory
