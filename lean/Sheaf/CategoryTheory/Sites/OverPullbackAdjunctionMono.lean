module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] public section

universe u

namespace CategoryTheory

/-- Extension by zero along `Over.forget W` exists on abelian sheaves and preserves
monomorphisms.  It is obtained by sheafifying the sectionwise direct-sum extension;
see Stacks Project, Lemmas 03DI--03DJ.
(blueprint: new-over-pullback-adjunction-mono)
-/
theorem overPullback_extensionByZero
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    (W : C) [HasSheafify (J.over W) AddCommGrpCat.{u}] :
    ∃ (L : Sheaf (J.over W) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}),
      Nonempty (L ⊣ J.overPullback AddCommGrpCat.{u} W) ∧ L.PreservesMonomorphisms := by
  sorry

end CategoryTheory
