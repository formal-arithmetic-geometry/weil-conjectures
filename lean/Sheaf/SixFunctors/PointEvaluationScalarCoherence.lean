/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module
public import Sheaf.SixFunctors.PointEvaluationScalarTensor

/-! Source: Stacks 0991, 03EL, 07A4
(blueprint: def-sf-point-evaluation-scalar-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.PointEvaluation
variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
variable {B}
/-- The specified scalar square, including preservation of its resolving models.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-point-evaluation-scalar-coherence). -/
structure ScalarCoherent
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') (T : TensorModel B) (T' : TensorModel B')
    (S : ScalarModel a T T') : Prop where
  /-- The actual chain square between evaluation and coefficient tensor comparisons. -/
  tensor_square : ∀ P Q : Complexes B,
    (complexSections k B').map (epsilon.{u + 1, u + 1, u} a P Q).hom ≫
        (T'.b ((extend.{u + 1, u + 1, u} a).obj P) ((extend.{u + 1, u + 1, u} a).obj Q)).hom ≫
        (S.κ.hom.app P ⊗ₘ S.κ.hom.app Q) =
      S.κ.hom.app (totalObj B P Q) ≫ (moduleExtend B a).map (T.b P Q).hom ≫
        (S.ε ((complexSections k B).obj P) ((complexSections k B).obj Q)).hom
  /-- Scalar extension sends resolving models to resolving models, even for nonflat a. -/
  sheaf_resolving : ∀ P : Complexes B, resolving B P → resolving B' ((extend.{u + 1, u + 1, u}
    a).obj P)
  /-- The ordinary scalar extension has the same K-flat computation property. -/
  module_resolving : ∀ P : CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ,
    moduleResolving B P → moduleResolving B' ((moduleExtend B a).obj P)



end AlgebraicGeometry.ProEtale.PointEvaluation
