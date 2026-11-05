/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorHorizontalSections
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Horizontal compatibility of the ordinary geometric tensor comparison

Source: Zheng Construction 4.1; Stacks 03EL.
(blueprint: lem-coef-geometric-tensor-component-horizontal)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] evaluation transition tensorSection ordinaryEvaluationTensor
attribute [local irreducible] coefficientMap systemRing evalSection rings ringPresheaf
attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence Prod.sectR
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] SheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalarsObj
attribute [local implicit_reducible] PresheafOfModules.presheaf ModuleCat.restrictScalars
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)

variable (μ : ∀ (n : ℕ) (M N : Mod.{c, v, max c v r} J (B n)),
  (O.inverseImage n).modules.obj (ordinaryTensor.{c, v, r} J (B n) M N) ≅
    ordinaryTensor.{c, v, r} J' (O.coefficients n)
      ((O.inverseImage n).modules.obj M) ((O.inverseImage n).modules.obj N))

/-- The forced component of the system tensor comparison.
Source: Zheng Construction 4.1; Stacks 03EL.
(blueprint: lem-coef-geometric-tensor-component-horizontal). -/
@[irreducible] def geometricTensorComponent (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ) :
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
        (O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N)) ≅
      (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
          (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
          (O.pull.obj M) (O.pull.obj N)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O.coefficients n)
  let := SheafOfModules.monoidalCategory (O.coefficients n)
  exact (O.ordinaryPullEvaluation n).app _ ≪≫
    (O.inverseImage n).modules.mapIso (ordinaryEvaluationTensor.{c, v, r} J B τ n M N) ≪≫
    μ n ((evaluation.{c, v, max c v r} J B τ n).obj M)
      ((evaluation.{c, v, max c v r} J B τ n).obj N) ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      ((O.ordinaryPullEvaluation n).app M).symm
      ((O.ordinaryPullEvaluation n).app N).symm ≪≫
    (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
      (O.pull.obj M) (O.pull.obj N)).symm

end WeilConjectures.SemilinearSections
