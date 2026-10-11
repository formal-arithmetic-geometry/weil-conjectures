/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.QuasiIso

/-! # Global sections of a resolution of the direct image of injectives

Source: Stacks Project, Cohomology of Sheaves, Tags 01FB, 01EZ, 01F0, 01EX;
Derived Categories, Tag 015E
(blueprint: lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections of a quasi-isomorphism from the direct image of a nonnegative complex
of injective modules to a nonnegative complex of injective modules is a quasi-isomorphism,
both over `O_Y(Y)` (Mathlib's `SheafOfModules.evaluation` at `⊤`, as in
`RingedSpace.globalSectionsFunctor`) and after forgetting to abelian groups.

The source has terms `(h_* I^n)(Y) = I^n(h⁻¹ Y) = I^n(X)` by
`pushforward_obj_obj`; its differentials are those of `I` on `X` by `pushforward_map_app`.
The `O_Y(Y)`-action on these terms is restriction along the structure-sheaf map of `h`.
Source: Stacks Project, Tags 01FB, 01EZ, 01F0, 01EX, 015E
(blueprint: lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso).

Proof: (1) In the abelian category of module sheaves, global sections is additive and
left exact by sectionwise computation of limits
(`lem-weil-pbc-module-sheaves-limits-sectionwise`). Enough injectives is supplied by
`lem-weil-pbc-scheme-modules-enough-injectives`.
(2) Every term of the direct image of `I` is acyclic for global sections by
`lem-weil-pbc-module-pushforward-injective-acyclic` (01EX, with the whole space as open).
Additivity of pushforward preserves its zero terms in negative degrees.
(3) Every term of `J` is acyclic by `lem-weil-pbc-derived-functor-injective-vanishing`.
(4) Apply `lem-weil-pbc-leray-acyclicity-quasi-iso` (015E) to the given quasi-isomorphism
between these two nonnegative complexes of acyclic objects.
(5) Identify sections of the direct image with sections on `X` by the formulas above.
Forgetting scalars preserves kernels, images and cokernels, so the induced maps on
cohomology are also bijective as maps of abelian groups. -/
theorem quasiIso_globalSections_pushforward_injectives
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (I : CochainComplex X.Modules ℤ) (J : CochainComplex Y.Modules ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) (hJ : ∀ n : ℤ, Injective (J.X n))
    (hI0 : ∀ n : ℤ, n < 0 → IsZero (I.X n))
    (hJ0 : ∀ n : ℤ, n < 0 → IsZero (J.X n))
    (φ : ((pushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (hφ : QuasiIso φ) :
    QuasiIso (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
      (op (⊤ : Y.Opens))).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ∧
      QuasiIso (((SheafOfModules.evaluation.{u} Y.ringCatSheaf (op (⊤ : Y.Opens)) ⋙
        forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (op (⊤ : Y.Opens))))
          AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
