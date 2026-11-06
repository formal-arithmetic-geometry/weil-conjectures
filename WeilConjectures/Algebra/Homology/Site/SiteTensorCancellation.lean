/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.PoincareDuality.TensorTrilinearUniversal

/-! # Cancellation in the explicit site tensor presentation

Source: Stacks 03EK and 0B8N, tensor comparison and evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max uC vC r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  (R : Sheaf J CommRingCat.{max uC vC r})
attribute [local instance 2000] cochainModulesMonoidal

private def tensorToSite (N : LineEvaluation.Modules.{uC, vC, r} R) :
    tensorRight N ≅ siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} (A :=
      R) N :=
  NatIso.ofComponents
    (fun M ↦ ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M N)
    (by
      intro M M' f
      apply LineEvaluation.pure_hom_ext.{uC, vC, r}
        (R)
      intro U x y
      have hf := LineEvaluation.pure_map.{uC, vC, r}
        (R) f (𝟙 N) U x y
      rw [tensorHom_id] at hf
      change (ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M' N).hom.val.app U
          (((tensorRight N).map f).val.app U
            (LineEvaluation.pureTensor.{uC, vC, r} _ M N U x y)) =
        ((siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} N).map f).val.app U
          ((ScalarHomOrdinary.tensorIsoSite.{uC, vC, max uC vC r} _ M N).hom.val.app U
            (LineEvaluation.pureTensor.{uC, vC, r} _ M N U x y))
      have hf' : ((tensorRight N).map f).val.app U
          (LineEvaluation.pureTensor.{uC, vC, r} _ M N U x y) =
          LineEvaluation.pureTensor.{uC, vC, r} _ M' N U (f.val.app U x) y := by
        simpa only [tensorRight, curriedTensor, Functor.flip, id_val,
          PresheafOfModules.id_app, ModuleCat.id_apply]
          using hf
      exact (congrArg
        ((ScalarHomOrdinary.tensorIsoSite _ M' N).hom.val.app U) hf').trans
        ((ScalarHomOrdinary.tensorIsoSite_pure _ M' N U
          (f.val.app U x) y).trans
          ((congrArg (((siteSheafTensorRight N).map f).val.app U)
            (ScalarHomOrdinary.tensorIsoSite_pure _ M N U x y)).trans
            (map_tmul_first _ f U x y)).symm))

private def siteCancel (P Q : LineEvaluation.Modules.{uC, vC, r} R)
    (e : P ⊗ Q ≅ unit
      ((sheafCompose (J)
        (forget₂ CommRingCat RingCat)).obj (R))) :
    siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} P ⋙
      siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} Q ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (tensorToSite R P).symm
      (siteSheafTensorRight.{vC, uC, max uC vC r, max uC vC r} Q) ≪≫
    Functor.isoWhiskerLeft (tensorRight P) (tensorToSite R Q).symm ≪≫
      LineEvaluation.cancellation.{uC, vC, r}
        (R) P Q e

attribute [local irreducible] tensorToSite siteCancel

end SheafOfModules
