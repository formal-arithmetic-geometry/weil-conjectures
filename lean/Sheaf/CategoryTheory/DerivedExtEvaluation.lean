module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Evaluation of an Ext class under a right derived functor

Source: Stacks Project, Derived Categories, Tag 05RR; canonical right-derived functor
and single-object normalization used in Cohomology on Sites, Tags 03FD and 01FT.
(blueprint: def-weil-pbc-derived-ext-evaluation).
-/

@[expose] public section
universe u v w t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace CategoryTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Apply derived global evaluation to a represented Ext morphism and a degree-zero section.
Source: Stacks Project, Tags 03FD and 01FT
(blueprint: def-weil-pbc-derived-ext-evaluation). -/
def derivedExtEvaluation {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory.{t} C] [HasExt.{u + 1} C]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (P : C ⥤ AddCommGrpCat.{u + 1}) [P.Additive] [PreservesFiniteLimits P]
    (A B : C) (q : ℕ) (g : P.obj A) (x : Ext A B q) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (P.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj B))) := by
  let e := P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
    P.rightDerivedZeroIsoSelf.app A
  let t := (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
    (P.rightDerivedFunctor.map (Ext.homEquiv x) ≫
      (P.rightDerivedFunctor.commShiftIso (q : ℤ)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj B))
  let h := ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso
    (q : ℤ) 0 (q : ℤ) (add_zero (q : ℤ))).hom.app
      (P.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B))
  exact (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
    (P.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app B))
      (h (t (e.inv g)))


end
end CategoryTheory
