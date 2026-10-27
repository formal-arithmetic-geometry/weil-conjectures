/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletionUnitModels
import all Sheaf.Paper.CoefficientExtensionFiniteAssociation
import all Sheaf.Paper.IntegralComparisonSequenceSystems
import Sheaf.Paper.ScalarDataExistence
import Sheaf.Paper.ScalarEvaluationTransposeExistence
import Sheaf.CategoryTheory.SystemScalarPackageExists

/-! # Fixed ordinary scalar models

Source: Stacks 03D7, 03EK and 06YY. Proof helpers for the strict scalar tower comparison.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe c v r t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof

private theorem fixedScalarData
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} φ) :
    ∃ A : SemilinearSections.ScalarData.{c, v, max c v r} φ, A.model = D := by
  obtain ⟨A, hA⟩ := SequenceScalarConstruction.scalarPackageExists φ D
  refine ⟨{ model := A.model
            ordinaryAdjunction := A.ordinaryAdj
            unit_section := ?_
            adjunction := A.adjunction
            transpose_model := ?_ }, hA⟩
  · intro M U x
    rw [A.unit_normalized]
    dsimp only [SheafOfModules.systemModelTmul]
    rw [one_smul]
    have hh : eqToHom (A.model.obj_eq M).symm ≫ eqToHom (A.model.obj_eq M) =
        𝟙 _ := by simp
    exact congrArg (fun f ↦ f.val.app U
      (SemilinearSections.extensionUnit.{c, v, max c v r} φ M U x)) hh
  · intro P Q _ f
    rw [A.transpose]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _

private theorem transportModel_E
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
    {φ ψ : R ⟶ S} (h : φ = ψ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} φ) :
    (h ▸ D).E = D.E := by
  subst ψ
  rfl

private theorem transportModel_heq
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
    {φ ψ : R ⟶ S} (h : φ = ψ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} φ) :
    HEq (h ▸ D) D := by
  subst ψ
  rfl

private theorem modelTensor_unit
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
    {φ ψ : R ⟶ S} (hφ : φ = ψ)
    (A : SemilinearSections.ScalarData.{c, v, max c v r} φ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r,
      max c v (max c v r + 1), max c v (max c v r + 1)} ψ)
    (hD : HEq A.model D)
    (N : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : N.val.obj U) :
    HEq (SheafOfModules.systemModelTmul D N U s x)
      (s • (show (A.model.E.obj N).val.obj U from
        (A.ordinaryAdjunction.unit.app N).val.app U x)) := by
  subst ψ
  have hh : A.model = D := eq_of_heq hD
  subst D
  apply heq_of_eq
  change s • SemilinearSections.scalarExtensionSection.{c, v, r} φ A N U x = _
  rw [scalarSection_eq_unit.{c, v, r}]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  integralComparisonSequenceScalarModel

private theorem scalarMap_eq :
    SemilinearSections.systemMap.{t + 1, t, max (t + 1) u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W) =
    integralComparisonSequenceScalarMap l E L ι W := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact (SemilinearSections.systemMap_existsUnique.{t + 1, t, max (t + 1) u}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)).exists.choose_spec
      U.unop.1 (op U.unop.2)

/-- Scalar systems whose sequence model is the prescribed actual cochain model.
Source: Stacks 03D7 and 03EK.
(blueprint: lem-trf-ordinary-quotient-fixed-scalar-systems).
Proof: identify the two sequence ring maps on components, transport the fixed
model, and use its normalized scalar package. Choose the finite scalar packages
and apply scalar evaluation transpose. The prescribed model equality and the
normalized ordinary unit compute the tensor section, including its section casts. -/
private theorem fixedSystems_exists :
    ∃ A : CoefficientExtensionSystems l E L ι W,
      A.scalar.model.E = (integralComparisonSequenceScalarModel l E L ι W).E ∧
      ∀ (N : coefficientSequenceModules l E W) (U : (ℕ × W.ProEt)ᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L W).obj.obj U) (x : N.val.obj U),
        HEq (integralComparisonSequenceTensorSection l E L ι W N U s x)
          (s • (show (A.scalar.model.E.obj N).val.obj U from
            (A.scalar.ordinaryAdjunction.unit.app N).val.app U x)) := by
  classical
  let J := Scheme.ProEt.topology W
  let B := integralCoefficientCommRingSheaf l E W
  let τ := coefficientSequenceCommRingTransition l E W
  let F := integralCoefficientCommRingSheaf l L W
  let σ := coefficientSequenceCommRingTransition l L W
  let α := integralScalarQuotientSheafMap l E L ι W
  let hα := coefficientExtensionQuotient_naturality l E L ι W
  let φ := SemilinearSections.systemMap.{t + 1, t, max (t + 1) u} J B τ F σ α hα
  let D := integralComparisonSequenceScalarModel l E L ι W
  have hφ : φ = integralComparisonSequenceScalarMap l E L ι W := scalarMap_eq l E L ι W
  let := SemilinearSections.hasDerived.{t + 1, t, max (t + 1) u}
    (coefficientSequenceTopology J) (SemilinearSections.systemRing.{t + 1, t, max (t + 1) u} J B τ)
  let := SemilinearSections.hasDerived.{t + 1, t, max (t + 1) u}
    (coefficientSequenceTopology J) (SemilinearSections.systemRing.{t + 1, t, max (t + 1) u} J F σ)
  let D' : SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max (t + 1) u,
      max (t + 2) (u + 1), max (t + 2) (u + 1)} φ := hφ.symm ▸ D
  obtain ⟨S, hS⟩ := fixedScalarData.{t + 1, t, u} (coefficientSequenceTopology J) φ D'
  obtain ⟨_, hL⟩ := SemilinearSections.semilinearScalarData.{t + 1, t, u} J B τ F σ α hα
  let levels := fun n ↦ (hL n).some
  obtain ⟨ev⟩ := SemilinearSections.semilinearScalarEvaluationTranspose.{t + 1, t, u}
    J B τ F σ α hα S levels
  refine ⟨{ scalar := S
            levels := levels
            evaluation := ev.evaluation
            transpose_evaluation := ev.transpose_evaluation }, ?_⟩
  constructor
  · change S.model.E = D.E
    rw [hS]
    exact transportModel_E.{t + 1, t, u} (coefficientSequenceTopology J) hφ.symm D
  · intro N U s x
    have hD : HEq S.model D := (heq_of_eq hS).trans
      (transportModel_heq.{t + 1, t, u} (coefficientSequenceTopology J) hφ.symm D)
    exact (heq_of_eq (sequenceTensorSection_eq l E L ι W N U s x)).trans
      (modelTensor_unit.{t + 1, t, u} (coefficientSequenceTopology J) hφ S D hD N U s x)

end OrdinaryScalarTowerProof
end WeilConjectures
