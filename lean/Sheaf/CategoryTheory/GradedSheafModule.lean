module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization

/-! # Graded left modules over a sheaf algebra

Source: Stacks Project, sdga.tex, definition-gm (Tag 0FR0 context), left-module convention
(blueprint: def-sfb-graded-sheaf-module-category).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafDg

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (S : Sheaf J CommRingCat.{w})

/-- Integer-graded coefficient-module sheaves, with the usual convolution tensor.
Source: Stacks, sdga.tex, definition-gm
(blueprint: def-sfb-graded-sheaf-module-category). -/
abbrev Graded := GradedObject ℤ (ringedSiteModules.{w} (rings S))

/-- The convolution tensor on graded module sheaves.
Source: Stacks, sdga.tex, definition-ga
(blueprint: def-sfb-graded-sheaf-module-category). -/
instance gradedMonoidal : MonoidalCategory (Graded S) := by
  unfold Graded rings ringedSiteModules
  exact GradedObject.monoidalCategory

/-- Associative unital graded sheaf algebras, without a differential.
Source: Stacks, sdga.tex, definition-ga
(blueprint: def-sfb-graded-sheaf-module-category). -/
abbrev GradedAlgebra := Mon (Graded S)

/-- The ordinary underlying graded functor is monoidal for the total tensor.
Its tensor comparison is the identity and its unit comparison is the standard
single-degree-zero identification. Source: Stacks, sdga.tex, definition-dga
(blueprint: def-sfb-graded-sheaf-module-category). -/
instance forgetComplexMonoidal :
    (HomologicalComplex.forget (ringedSiteModules.{w} (rings S))
      (ComplexShape.up ℤ)).Monoidal := by
  exact @Monoidal.fromInducedMonoidal (Graded S) _ (gradedMonoidal S)
    (Complex S) _ (complexMonoidal S).toMonoidalCategoryStruct
    (HomologicalComplex.forget (ringedSiteModules.{w} (rings S)) (ComplexShape.up ℤ))
    inferInstance (HomologicalComplex.Monoidal.inducingFunctorData
      (ringedSiteModules.{w} (rings S)) (ComplexShape.up ℤ))

variable {S}

/-- Forget the differential of a dg algebra, keeping its actual multiplication and unit.
Source: Stacks, sdga.tex, definition-dga
(blueprint: def-sfb-graded-sheaf-module-category). -/
def underlyingGradedAlgebra (A : Algebra S) : GradedAlgebra S :=
  (HomologicalComplex.forget (ringedSiteModules.{w} (rings S))
    (ComplexShape.up ℤ)).mapMon.obj A

/-- Graded left module sheaves: objects are graded sheaves with associative unital action;
morphisms are action-preserving degree-zero sheaf maps. No differential is present.
Source: Stacks, sdga.tex, definition-gm, left-module convention
(blueprint: def-sfb-graded-sheaf-module-category). -/
abbrev GradedLeftModule (A : GradedAlgebra S) := Mod (Graded S) A.X

end CategoryTheory.SheafDg
