/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.Paper.CoefficientExtensionReductionData
import all Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
import all Sheaf.Paper.IntegralScalarExtensionWellDefined

/-! # Strict representatives for finite coefficient extension

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
private theorem extensionIso_naturality
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})
    (α : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    {M N : SheafOfModules.SequenceProjection.Modules R} (f : M ⟶ N) (n : ℕ) :
    ((SheafOfModules.SequenceProjection.extension R B α).map f).app n ≫
        (SheafOfModules.SequenceProjection.extensionIso R B α N n).hom =
      (SheafOfModules.SequenceProjection.extensionIso R B α M n).hom ≫
        SheafOfModules.changeOfRingsHom (α.app (op n)) M f := by
  change (SheafOfModules.SequenceProjection.scalar R B α n).model.E.map f ≫
    eqToHom ((SheafOfModules.SequenceProjection.scalar R B α n).model.obj_eq N) = _
  rw [(SheafOfModules.SequenceProjection.scalar R B α n).model.map_eq]
  simp [SheafOfModules.SequenceProjection.extensionIso]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (A : CoefficientExtensionSystems l E L ι W)

private def scalarCoefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l L W :=
  NatTrans.ofOpSequence (fun n ↦ integralScalarRho l E L ι W n) (fun n ↦ by
    simp only [Functor.const_obj_map,
      coefficientSequenceCommRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    unfold integralScalarRho
    rw [Category.assoc, coefficientExtensionQuotient_naturality]
    erw [Category.id_comp]
    rw [← Category.assoc]
    apply congrArg (fun f ↦ f ≫ integralScalarQuotientSheafMap l E L ι W n)
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget₂ CommRingCat RingCat).map_injective
    change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U =
      (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app U ≫
        (integralCoefficientSheafTransition l E W n).hom.app U
    have h := congrArg (fun k ↦ k.hom.app U)
      (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
    simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)

private def scalarCoefficientExtension : scalarReductionSource l E W ⥤
    coefficientSequenceModules l L W :=
  SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W) ⋙
      SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)

private instance scalarCoefficientExtension_additive :
    (scalarCoefficientExtension l E L ι W).Additive := by
  unfold scalarCoefficientExtension
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let : G.Additive := ⟨by
    intro M N f g
    ext U x
    change (((f + g).app U.unop.1).val.app (op U.unop.2)) x = _
    have h := (SheafOfModules.systemEvaluation
      (coefficientSequenceCommRingSystem l L W) U.unop.1).map_add (f := f) (g := g)
    have hx := congrArg (fun f ↦ (f.val.app (op U.unop.2)) x) h
    exact hx⟩
  infer_instance

private theorem coefficientEvaluation_eq_system (n : ℕ) :
    coefficientSequenceEvaluation l L W n =
      SheafOfModules.systemSequenceEvaluation (coefficientSequenceCommRingSystem l L W) n := by
  unfold coefficientSequenceEvaluation SheafOfModules.systemSequenceEvaluation
  congr 1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private def scalarCoefficientEvaluation (n : ℕ) :
    scalarCoefficientExtension l E L ι W ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n := by
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let B := coefficientSequenceCommRingSystem l L W
  let a : F ⋙ G ⋙ coefficientSequenceEvaluation l L W n ≅
      F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n :=
    Functor.isoWhiskerLeft (F ⋙ G) (eqToIso (coefficientEvaluation_eq_system l L W n))
  let b : F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n ≅
      F ⋙ SheafOfModules.systemEvaluation B n :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.strictSystemSequenceUnitLevel B
      (F.obj M) n).symm) (by intros; ext U x; rfl)
  let c : F ⋙ SheafOfModules.systemEvaluation B n ≅
      integralScalarReduction l E L ι W n :=
    NatIso.ofComponents (fun M ↦
      SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) M n ≪≫
      eqToIso (by
        change SheafOfModules.changeOfRings (integralScalarRho l E L ι W n) M = _
        exact (integralScalarReduction_obj l E L ι W n M).symm))
      (by
        intro M N f
        dsimp only [Functor.comp_map, Iso.trans_hom, eqToIso.hom]
        rw [integralScalarReduction_map l E L ι W n f]
        have he := extensionIso_naturality
          (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) f n
        erw [← Category.assoc, he]
        dsimp only [SheafOfModules.SequenceProjection.extensionIso, eqToIso.hom]
        simp only [← Category.assoc, eqToHom_trans]
        rfl)
  exact a ≪≫ b ≪≫ c

/-- Simultaneous strict finite quotient representatives of derived coefficient extension.
Source: integral operations, Stacks 06YY, 07A6 and 0941
(blueprint: stage3-pur-extension-strict-representatives).
Proof: use the ringed sequence projection to form the ordinary strict system whose
nth term is tensor with the nth target quotient. Its tensor generators determine
its quotient transitions. Apply it degreewise to flat-term K-flat complexes.
The given balanced associations identify the evaluated complexes with the iterated
finite scalar models. Transpose the ordinary units, using the reduction unit and
scalar evaluation formulas, to obtain a natural comparison from the specified
derived extension. At each level this is the composite of the two universal
K-flat comparisons and the given association. Both scalar extensions preserve
K-flatness, so these comparisons are invertible. The jointly conservative
evaluations make the system comparison invertible. For m at least n, scalar
extension of the mth term to the nth quotient is identified with the nth term by
balanced tensor association. Its adjoint is precisely the specified quotient
transition. Thus the universal Hom criterion gives normalization, first on good
representatives and then on every derived object by a K-flat resolution. -/
theorem coefficientExtensionStrictRepresentative_exists
    (SE : CoefficientDerivedSystemCalculus l E W)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association) :
    ∃ (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
        CochainComplex (coefficientSequenceModules l L W) ℤ)
      (directEvaluation : ∀ n : ℕ,
        direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
          (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
      (model : integralOperationsGoodLocalization l E W ⋙
        coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q),
      IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation ∧
      IsCoefficientExtensionModelEvaluation l E L ι W SE A association direct
        directEvaluation model ∧
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        IsNormalizedCoefficientSequence l L W
          ((coefficientExtensionSystem l E L ι W SE A).obj K) := by
  sorry

end WeilConjectures
