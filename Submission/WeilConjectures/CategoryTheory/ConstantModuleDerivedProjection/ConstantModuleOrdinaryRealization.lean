/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleDerivedComparisonData
import all Submission.WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleGeometricComparisonData
import Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import Mathlib.CategoryTheory.Monoidal.Functor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary constant-module realization of a geometric inverse image

Source: Stacks Project, Sites, Tag 00YV (6), Modules on Sites, Tag 03EL,
and Cohomology on Sites, Tag 07A4
(blueprint: lem-sfb-constant-module-ordinary-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option linter.privateModule false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CategoryTheory.ConstantScalarRestriction.fixedSymmetric
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open SheafOfModules
namespace CategoryTheory.ConstantModuleDerivedProjection
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]

-- Cache the standard sheafification properties before the repeated section calculations.
private instance cachedWeakComm (J : GrothendieckTopology C) :
    HasWeakSheafify J CommRingCat.{max u v} := inferInstance

private instance cachedWeakRing (J : GrothendieckTopology C) :
    HasWeakSheafify J RingCat.{max u v} := inferInstance

private instance cachedForgetRing (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  inferInstance

attribute [local irreducible] presheafToSheaf

private def scalarValue (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (U : Cᵒᵖ) (b : B) : (ring J B).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b

private def scalarSection
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (b : B) :
    (constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1} ⟶
      (sheafCompose J (forget CommRingCat.{max u v})).obj (ring J B) :=
  (constantSheaf J (Type (max u v))).map (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget CommRingCat.{max u v})).inv.app (CommRingCat.of B)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 100000 in
-- Compare the commutative-ring and ring sheafification units.
private theorem restriction_scalar (M : Modules J A) (U : Cᵒᵖ) (a : A)
    (x : M.val.obj U) :
    @SMul.smul A (((restriction J A).obj M).obj.obj U) inferInstance a x =
      scalarValue J A U a • x := by
  dsimp only [scalarValue]
  change ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
    (CommRingCat.of A)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) • x = _
  congr 1
  have hf := congrArg (fun f ↦ f.app U a)
    (sheafComposeIso_hom_fac J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
  have hp := congrArg (fun f ↦ f.app U a) (toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).hom.app (CommRingCat.of A)))
  dsimp at hp
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) _ = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) z) hp.symm).trans hf

end CategoryTheory.ConstantModuleDerivedProjection
