module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

open CategoryTheory Limits

theorem DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self_stub
    {R : Type v} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
    {T : Type*} [Category T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated T]
    (F G : DerivedCategory (ModuleCat.{v} R) ⥤ T) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (h : IsIso (τ.app ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R)))) :
    IsIso τ := sorry
