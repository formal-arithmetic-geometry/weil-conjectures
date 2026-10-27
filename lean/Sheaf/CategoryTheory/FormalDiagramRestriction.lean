module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-! # Formal diagrams and cartesian restriction

Source: Stacks Project, artin.tex, equation-approximation and its preceding definition
of formal objects (blueprint: def-sfb-formal-diagram-restriction).

A formal object retains every transition, its identity and composition laws, and all
automorphisms. A restriction model retains the cartesian arrows to the original object;
these arrows characterize the functor up to unique compatible natural isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe uB vB uC vC uI vI

namespace CategoryTheory

variable {B : Type uB} [Category.{vB} B] {I : Type uI} [Category.{vI} I]

/-- The category of lifts of a base diagram, with natural transformations over its
identity. For a category fibred in groupoids this is the groupoid of formal systems.
Source: Stacks, artin.tex, equation-approximation
(blueprint: def-sfb-formal-diagram-restriction). -/
abbrev FormalDiagram (F : BasedCategory.{vC, uC} B) (D : I ⥤ B) :=
  Functor.Fiber ((Functor.whiskeringRight I F.obj B).obj F.p) D

/-- A canonical restriction functor is equipped with its cartesian arrows, compatible
with every transition and natural in the original object. Thus it is not an arbitrary
functor to an abstractly equivalent category.
Source: Stacks, artin.tex, equation-approximation
(blueprint: def-sfb-formal-diagram-restriction). -/
structure FormalRestrictionModel (F : BasedCategory.{vC, uC} B) (D : I ⥤ B)
    (T : B) (ι : D ⟶ (Functor.const I).obj T) where
  restriction : Functor.Fiber F.p T ⥤ FormalDiagram F D
  arrow (x : Functor.Fiber F.p T) (i : I) :
    ((restriction.obj x).val.obj i) ⟶ x.val
  cartesian (x : Functor.Fiber F.p T) (i : I) :
    F.p.IsStronglyCartesian (ι.app i) (arrow x i)
  transition (x : Functor.Fiber F.p T) {i j : I} (h : i ⟶ j) :
    (restriction.obj x).val.map h ≫ arrow x j = arrow x i
  naturality {x y : Functor.Fiber F.p T} (h : x ⟶ y) (i : I) :
    (restriction.map h).val.app i ≫ arrow y i = arrow x i ≫ h.val

end CategoryTheory
