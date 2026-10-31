/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientClosedTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Signed cancellation in an arbitrary normalized closed tensor presentation

Source: Stacks 0A8X and 08JC. The native tensor shifts are transported through the
canonical evaluation-preserving comparison of closed tensor presentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite WeilConjectures SheafOfModules

namespace CategoryTheory.RingedSignedTensor

private theorem cancellation_natural_aux
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int]
    (K : D) {P Q : D} (f : P ⟶ Q) (n : ℤ) :
    (T.map (f⟦n⟧')).app (K⟦-n⟧) ≫
        ((T.obj (Q⟦n⟧)).commShiftIso (-n)).hom.app K ≫
        (((T.flip.obj K).commShiftIso n).hom.app Q)⟦-n⟧' ≫
        (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app _ =
      (((T.obj (P⟦n⟧)).commShiftIso (-n)).hom.app K ≫
        (((T.flip.obj K).commShiftIso n).hom.app P)⟦-n⟧' ≫
        (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app _) ≫
          (T.map f).app K := by
  have h₁ := NatTrans.shift_app_comm (T.map (f⟦n⟧')) (-n) K
  have h₂ := (T.flip.obj K).commShiftIso_hom_naturality f n
  change (T.map (f⟦n⟧')).app K ≫
      ((T.flip.obj K).commShiftIso n).hom.app Q =
    ((T.flip.obj K).commShiftIso n).hom.app P ≫ ((T.map f).app K)⟦n⟧' at h₂
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp]
  simp only [Category.assoc]
  have hc := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.naturality
    ((T.map f).app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  erw [hc]
  rfl

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The native ringed module category.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
abbrev Modules := RingedDerivedNative.Modules.{c, v, r} J R

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- The native tensor, with the monoidal presentation explicitly retained.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeTensor : DerivedCategory (Modules.{c, v, r} J R) ×
    DerivedCategory (Modules.{c, v, r} J R) ⥤ DerivedCategory (Modules.{c, v, r} J R) :=
  @tensor _ _ (RingedDerivedNative.monoidal.{c, v, r, w} J R)

/-- The native tensor in curried form.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeCurriedTensor : DerivedCategory (Modules.{c, v, r} J R) ⥤
    DerivedCategory (Modules.{c, v, r} J R) ⥤ DerivedCategory (Modules.{c, v, r} J R) :=
  @curriedTensor _ _ (RingedDerivedNative.monoidal.{c, v, r, w} J R)

/-- The canonical two-variable shifts of the native total derived tensor.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
@[instance_reducible]
def nativeTensorShift : (nativeCurriedTensor.{c, v, r, w} J R).CommShift₂Int := by
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesSymmetric R
  letI := SheafOfModules.cochainModulesPreadditive R
  letI := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  letI := SheafOfModules.hasFunctorialFlatResolution_kfi R
  exact DerivedCategory.commShift₂CurriedTensor (Modules.{c, v, r} J R)

/-- Opposite shifts cancel with the Hom argument in the first tensor slot.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeCancellation (K P : DerivedCategory (Modules.{c, v, r} J R)) (n : ℤ) :
    (nativeTensor.{c, v, r, w} J R).obj (P⟦n⟧, K⟦-n⟧) ⟶
      (nativeTensor.{c, v, r, w} J R).obj (P, K) :=
  let T := nativeCurriedTensor.{c, v, r, w} J R
  letI := nativeTensorShift.{c, v, r, w} J R
  ((T.obj (P⟦n⟧)).commShiftIso (-n)).hom.app K ≫
    (((T.flip.obj K).commShiftIso n).hom.app P)⟦-n⟧' ≫
      (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app _

/-- The proved native closed structure, retaining its recorded evaluation model.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeClosed :
    CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R) :=
  (RingedDerivedNative.closedAdjunction.{c, v, r, w} J R).choose

/-- The closed structure uses exactly the native monoidal structure.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
theorem nativeClosed_monoidal :
    (nativeClosed.{c, v, r, w} J R).monoidal = RingedDerivedNative.monoidal.{c, v, r, w} J R :=
  (RingedDerivedNative.closedAdjunction.{c, v, r, w} J R).choose_spec.1

/-- The evaluation-preserving comparison with the native tensor.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def comparison
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)) :
    S.tensor ≅ nativeTensor.{c, v, r, w} J R :=
  CoefficientClosedStructure.comparison S (nativeClosed.{c, v, r, w} J R) ≪≫
    eqToIso (congrArg (fun m ↦ @tensor _ _ m) (nativeClosed_monoidal.{c, v, r, w} J R))

/-- Evaluation for the native tensor, with the closed-presentation equality explicit.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def nativeEvaluation (K M : DerivedCategory (Modules.{c, v, r} J R)) :
    (nativeTensor.{c, v, r, w} J R).obj
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M), K) ⟶ M :=
  (eqToIso (congrArg (fun m ↦ @tensor _ _ m)
    (nativeClosed_monoidal.{c, v, r, w} J R))).inv.app _ ≫
      (nativeClosed.{c, v, r, w} J R).evaluation K M

/-- The native comparison preserves the actual evaluation counit.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
theorem comparison_evaluation
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (K M : DerivedCategory (Modules.{c, v, r} J R)) :
    (comparison.{c, v, r, w} J R S).hom.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M), K) ≫
      nativeEvaluation.{c, v, r, w} J R K M = S.evaluation K M := by
  simp only [comparison, nativeEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  exact CoefficientClosedStructure.comparison_evaluation S
    (nativeClosed.{c, v, r, w} J R) K M

/-- Signed opposite-shift cancellation, transported to the supplied closed tensor.
The quadratic sign is the correction in the exact contravariant Hom shift.
Source: Stacks 0A8X and 08JC.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2). -/
def cancellation
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (K P : DerivedCategory (Modules.{c, v, r} J R)) (n : ℤ) :
    S.tensor.obj (P⟦n⟧, K⟦-n⟧) ⟶ S.tensor.obj (P, K) :=
  (n * (n + 1) / 2).negOnePow •
    ((comparison.{c, v, r, w} J R S).hom.app (P⟦n⟧, K⟦-n⟧) ≫
      nativeCancellation.{c, v, r, w} J R K P n ≫ (comparison.{c, v, r, w} J R S).inv.app (P, K))

/-- Cancellation is natural in the Hom-valued tensor argument.
Source: Stacks 08JC; naturality of the two tensor shifts and of shift cancellation.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2).
Proof: move the shifted map through the second-slot tensor shift, then through
its first-slot shift. Naturality of the shift-composition isomorphism cancels the
opposite shifts. Conjugation by the closed-tensor comparison and the integer-unit
sign preserve the resulting square. -/
theorem cancellation_natural
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (K : DerivedCategory (Modules.{c, v, r} J R))
    {P Q : DerivedCategory (Modules.{c, v, r} J R)} (f : P ⟶ Q) (n : ℤ) :
    S.tensor.map (Prod.mkHom (f⟦n⟧') (𝟙 (K⟦-n⟧))) ≫ cancellation.{c, v, r, w} J R S K Q n =
      cancellation.{c, v, r, w} J R S K P n ≫ S.tensor.map (Prod.mkHom f (𝟙 K)) := by
  let T := nativeCurriedTensor.{c, v, r, w} J R
  letI := nativeTensorShift.{c, v, r, w} J R
  have hn : (nativeTensor.{c, v, r, w} J R).map (Prod.mkHom (f⟦n⟧') (𝟙 (K⟦-n⟧))) ≫
      nativeCancellation.{c, v, r, w} J R K Q n =
    nativeCancellation.{c, v, r, w} J R K P n ≫
      (nativeTensor.{c, v, r, w} J R).map (Prod.mkHom f (𝟙 K)) := by
    simpa only [T, nativeTensor, nativeCancellation, nativeCurriedTensor,
      tensor_map, tensorHom_id, curriedTensor_map_app] using
      cancellation_natural_aux T K f n
  simp only [cancellation, Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc]
  congr 1
  rw [reassoc_of% ((comparison.{c, v, r, w} J R S).hom.naturality
    (Prod.mkHom (f⟦n⟧') (𝟙 (K⟦-n⟧)))), reassoc_of% hn]
  rw [(comparison.{c, v, r, w} J R S).inv.naturality]

/-- An evaluation identity in the native tensor transports to any closed presentation.
Source: uniqueness of left adjoints and naturality of the closed tensor comparison.
(blueprint: lem-sfb-ringed-tensor-signed-cancellation-Y2).
Proof: precompose the native identity with the tensor comparison. Its naturality
moves the specified Hom comparison through it. The comparison preserves evaluation;
its inverse at the unshifted pair gives the transported cancellation map. -/
theorem evaluation_transport
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (K M : DerivedCategory (Modules.{c, v, r} J R)) (n : ℤ)
    (s : ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M))⟦n⟧ ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op (K⟦-n⟧), M))
    (h : (nativeTensor.{c, v, r, w} J R).map (Prod.mkHom s (𝟙 (K⟦-n⟧))) ≫
        nativeEvaluation.{c, v, r, w} J R (K⟦-n⟧) M =
      (n * (n + 1) / 2).negOnePow •
        (nativeCancellation.{c, v, r, w} J R K
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M)) n ≫
          nativeEvaluation.{c, v, r, w} J R K M)) :
    S.tensor.map (Prod.mkHom s (𝟙 (K⟦-n⟧))) ≫ S.evaluation (K⟦-n⟧) M =
      cancellation.{c, v, r, w} J R S K
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, M)) n ≫
        S.evaluation K M := by
  rw [← comparison_evaluation J R S (K⟦-n⟧) M]
  rw [← Category.assoc, (comparison.{c, v, r, w} J R S).hom.naturality,
    Category.assoc, h]
  simp only [cancellation, Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc]
  congr 1
  rw [← comparison_evaluation J R S K M]
  simp only [Iso.inv_hom_id_app_assoc]

end CategoryTheory.RingedSignedTensor
