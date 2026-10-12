/-
Copyright (c) 2026 The SHEAF contributors.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Left exactness of global sections on scheme modules

Source: literature/stacks-project/cohomology.tex, Cohomology of Sheaves, Lemma Tag 01EZ
(blueprint: lem-sc-global-sections-left-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The global sections functor on sheaves of modules over a scheme.

The value on a module is its sections over the whole scheme, regarded as an abelian group.
Source: literature/stacks-project/cohomology.tex, Cohomology of Sheaves, Lemma Tag 01EZ
(blueprint: lem-sc-global-sections-left-exact).
-/
noncomputable def globalSectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    (evaluation (TopologicalSpace.Opens (X : TopCat))ᵒᵖ AddCommGrpCat.{u}).obj
      (Opposite.op (⊤ : TopologicalSpace.Opens (X : TopCat)))

/-- Global sections is additive and preserves kernels, hence is left exact.

Proof (Stacks Project, Cohomology of Sheaves, Lemma Tag 01EZ). Kernels of morphisms of
sheaves of modules are computed sectionwise, so evaluating at the whole scheme preserves
kernels. Sections are abelian groups and finite products of sheaves of modules are computed
sectionwise, so evaluation is additive. Additivity together with kernel preservation is
left exact by `def-sp-left-exact-additive` (blueprint: lem-sc-global-sections-left-exact).
-/
theorem globalSectionsFunctor_additive_leftExact (X : Scheme.{u}) :
    (globalSectionsFunctor X).Additive ∧
      ∀ {M N : X.Modules} (f : M ⟶ N),
        PreservesLimit (parallelPair f 0) (globalSectionsFunctor X) := by
  unfold globalSectionsFunctor
  constructor
  · constructor
    intro M N f g
    rfl
  · intro M N f
    have : PreservesLimits (toPresheaf X) := inferInstance
    have : PreservesLimits ((evaluation (TopologicalSpace.Opens (X : TopCat))ᵒᵖ
        AddCommGrpCat.{u}).obj (Opposite.op (⊤ : TopologicalSpace.Opens (X : TopCat)))) :=
      inferInstance
    infer_instance

end AlgebraicGeometry.Scheme.Modules
