/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
public import Submission.WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Submission.WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Counit equation for canonical transport
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-equation). -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback

private theorem single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N =
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
        (F.obj N) ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (c.hom.app N) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.singleMapHomologicalComplex,
    HomologicalComplex.single, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplex]



end AlgebraicGeometry
