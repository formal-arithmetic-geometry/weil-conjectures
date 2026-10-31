/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomTensorAdjointNaturality
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletionSignedRepresentative
import all WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
import all WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletedInterchangeCanonical
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.IntegralHom.OrdinaryTensorAdjointRepresentative
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedModelExistence
import WeilConjectures.SixFunctors.IntegralOrdinary.TensorCompletionChainRingedIdentification
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletionChainNormalization
import all WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations

/-! # Ordinary-to-completed tensor and the adjoint comparison

Source: the normalized completion and evaluation argument in
thm-coef-rational-verdier.proof.md, paragraph 1
(blueprint: lem-sf-ordinary-completed-tensor-adjoint-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

attribute [local implicit_reducible] integralOperationsGoodComplex

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem generator_transport
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (i j k : ℤ) (h : i + j = k) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X) P Q i j k h U x y =
      (eqToHom (congrArg
        (fun n : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj P).obj Q).X n)
          h)).val.app U (IntegralHom.totalPair.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X) P Q i j U x y) := by
  subst k
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralHom.derivedCategory in
private theorem completion_unit_representative
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    ((pullbackTensorCalculus l E X).integralTensorModel.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (pullbackTensorCalculus l E X).integralClosed P.obj Q.obj
      P.property.1 Q.property.1).hom ≫
        podCompletedTensorUnit l E X (DerivedCategory.Q.obj P.obj)
          (DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      DerivedCategory.Q.map ((RationalVerdier.completionChain D l hl X E).app
        (P.obj, Q.obj)) := by
  obtain ⟨d, _⟩ := IntegralSystemRealization.integralRingedModelExistence l E
  let S := pullbackTensorCalculus l E X
  let ρ := (d.tensor X).ordinary.representative.hom.app
    (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩)
  let α := (eqToIso (congrArg (fun (T :
      DerivedCategory (integralTowerModules l E X) ×
        DerivedCategory (integralTowerModules l E X) ⥤
        DerivedCategory (integralTowerModules l E X)) ↦ T.obj
    (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) (d.tensorClosed X))).hom
  have hrep := d.tensorRepresentative X P.obj Q.obj P.property Q.property
  have ht := GeneratorReduction.tensor_augmentation_onGood l E d X P Q
  have hunit : α ≫ podCompletedTensorUnit l E X (DerivedCategory.Q.obj P.obj)
      (DerivedCategory.Q.obj Q.obj) =
      ((d.tensor X).chi l E).app (DerivedCategory.Q.obj P.obj,
        DerivedCategory.Q.obj Q.obj) := by
    apply (cancel_mono ((pullbackTensorIntegralTensorModel l E X).hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))).1
    rw [ht]
    dsimp only [podCompletedTensorUnit]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
    erw [Category.comp_id]
    have hn :=
      congrArg (fun z ↦ z ≫ (coefficientSequenceLimit l E X).map
        (S.reductionTensor.hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)))
        (S.adjunction.unit.naturality α)
    simp only [Functor.comp_map, Functor.id_map, Category.assoc, S, α,
      IntegralSystemRealization.calculus] at hn
    with_unfolding_all exact hn
  rw [← hrep]
  simp only [Category.assoc]
  erw [reassoc_of% hunit]
  have hc := (d.tensor X).canonical.2 P.obj Q.obj P.property Q.property
  rw [RationalVerdier.completionChain_eq_native D l hl X E,
    ← IntegralOrdinary.ringedTensorChain_eq_tensorCompletionChain l E X d]
  simpa only [OpenFactorCoherence.Tensor.chi, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] using hc

/-- The counit-preserving comparison of the ordinary left tensor with the canonical
right tensor commutes with the actual completion maps and signed braiding.
Source: thm-coef-rational-verdier.proof.md, paragraph 1; the normalized completion
and tensor-Hom evaluation argument, Stacks 08J9, 07A4, 099B.
Proof: compare the two ordinary tensors on K-flat representatives. Their tensor-Hom
counits have the same signed Hom-complex evaluation on every homogeneous local
pure tensor. Thus the comparison preserving those counits, namely leftAdjointUniq,
is the ordinary signed interchange followed by the tensor model comparison.
The completion representative equation identifies its composite with the actual
completion unit: both have the quotient image of each pure tensor in the first
Roos coordinate and zero in the shifted coordinate. The completed braiding has
exactly the corresponding signed interchange after coherent reduction. Faithful
coherent reduction and the K-flat localization extend the equality to all integral
constructible inputs. The construction also covers zero inputs and empty schemes.
(blueprint: lem-sf-ordinary-completed-tensor-adjoint-square). -/
theorem ordinaryCompletedTensor_adjoint_square
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (c : RationalVerdier.Completion D l hl X E a)
    (K N : sfIntegralConstructibleCategory l E X) :
    ((a.adjunction K.obj).leftAdjointUniq
      ((pullbackTensorCalculus l E X).integralClosed.adjunction K.obj)).hom.app N.obj ≫
        podCompletedTensorUnit l E X N.obj K.obj =
      c.map.app (K.obj, N.obj) ≫
        (@pullbackTensorIntegralBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) K N).hom.hom := by
  let S := pullbackTensorCalculus l E X
  let τ : S.integralClosed.tensor ⟶ integralCompletedTensor l E X :=
    { app := fun P ↦ podCompletedTensorUnit l E X P.1 P.2
      naturality := fun {P Q} f ↦ completedTensorUnit_naturality l E X
        P.1 P.2 Q.1 Q.2 f.1 f.2 }
  let e := IntegralFiniteExtension.tensorAdjointComparison l E X a
  let left := e.hom ≫ Functor.whiskerLeft (pullbackTensorSwap _) τ
  let right := c.map ≫ (RationalVerdier.completedSignedSwap l E X).hom
  have heq : left = right := by
    let q := integralOperationsGoodLocalization l E X
    let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E X
    apply Localization.natTrans_ext (q.prod q) (V.prod V)
    rintro ⟨P, Q⟩
    obtain ⟨s, hs, he⟩ := IntegralHom.tensorAdjointComparison_representative.{u, u}
      X (completedIntegralCommRingSheafUnrestricted l E X) a
      S.integralClosed S.integralTensorModel P.obj Q.obj P.property.1 Q.property.1
    have hs' : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
        (x : (P.obj.X i).val.obj U) (y : (Q.obj.X j).val.obj U),
        (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u}
          X (completedIntegralCommRingSheafUnrestricted l E X) P.obj Q.obj i j U x y) =
          (i * j).negOnePow •
            (eqToHom (congrArg
              (fun k : ℤ ↦ ((constructibleTensorTotal l E X).obj (Q.obj, P.obj)).X k)
                (add_comm j i))).val.app U
              (IntegralHom.totalPair.{u, u} X
                (completedIntegralCommRingSheafUnrestricted l E X) Q.obj P.obj j i U y x) := by
      intro i j U x y
      have h := hs i j (i + j) rfl (add_comm j i) U x y
      simp only [generator_transport, eqToHom_refl, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply] at h
      with_unfolding_all exact h
    have hc := eq_of_heq (c.representative P Q)
    have hu := completion_unit_representative D l hl X E Q P
    have hchain := RationalVerdier.completion_signed_representative D l hl X E P Q s hs'
    change e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      podCompletedTensorUnit l E X (DerivedCategory.Q.obj Q.obj)
        (DerivedCategory.Q.obj P.obj) =
      c.map.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (RationalVerdier.completedSignedSwap l E X).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
    apply (cancel_epi (a.representative.hom.app
      (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩))).1
    apply (cancel_mono ((integralCompletedTensorComparison l E X).hom.app (Q, P))).1
    simp only [Category.assoc]
    change S.integralTensorModel.comparison.hom.app
      (⟨Q.obj, Q.property.1⟩, ⟨P.obj, P.property.1⟩) ≫
        podCompletedTensorUnit l E X (DerivedCategory.Q.obj Q.obj)
          (DerivedCategory.Q.obj P.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (Q, P) = _ at hu
    erw [reassoc_of% he, hu]
    rw [hchain, ← hc]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have h := congrArg (fun t ↦ t.app (K.obj, N.obj)) heq
  change e.hom.app (K.obj, N.obj) ≫ podCompletedTensorUnit l E X N.obj K.obj =
    c.map.app (K.obj, N.obj) ≫
      (RationalVerdier.completedSignedSwap l E X).hom.app (K.obj, N.obj) at h
  rw [RationalVerdier.canonical_normalization D l hl X E K N]
  exact h

end WeilConjectures.RationalOperations
