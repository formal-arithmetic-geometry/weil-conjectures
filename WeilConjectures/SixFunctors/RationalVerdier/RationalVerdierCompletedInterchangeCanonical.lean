/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierPairingCalculus
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletionSignedRepresentative
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Canonical realization of normalized completed interchange

Source: blueprint thm-coef-rational-verdier, paragraph 3, signed transposition.
(blueprint: new-lem-coef-rational-verdier-completed-interchange-canonical).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open WeilConjectures
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

attribute [local implicit_reducible] coefficientSequenceInternalHom
  integralOperationsGoodComplex integralOperationsGoodLocalization pullbackTensorSwap
  pullbackTensorReferenceTensor integralOperationsTensorOnGood IntegralHom.totalTensor
  constructibleIntegralTensor

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem canonical_normalization
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K M : sfIntegralConstructibleCategory l E X) :
    (@pullbackTensorIntegralBraiding l _ E _ _ _ X (units D l hl X) K M).hom.hom =
      (completedSignedSwap l E X).hom.app (K.obj, M.obj) := by
  let := units D l hl X
  let e : (constructibleIntegralTensor l E X).obj (K, M) ≅
      (constructibleIntegralTensor l E X).obj (M, K) :=
    ObjectProperty.isoMk _ ((completedSignedSwap l E X).app (K.obj, M.obj))
  have he : (pullbackTensorCalculus l E X).reduction.map e.hom.hom ≫
        (pullbackTensorIntegralReductionTensor l E X M K).hom =
      (pullbackTensorIntegralReductionTensor l E X K M).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (pullbackTensorCalculus l E X).systemClosed
          (pullbackTensorCalculus l E X).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E X).reduction.obj K.obj,
             (pullbackTensorCalculus l E X).reduction.obj M.obj) := by
    dsimp only [e, completedSignedSwap, ObjectProperty.isoMk, ObjectProperty.homMk,
      pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.mapIso_hom, asIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [← Category.assoc
      ((pullbackTensorCalculus l E X).reduction.map
        ((pullbackTensorIntegralTensorModel l E X).inv.app (M.obj, K.obj)))
      ((pullbackTensorCalculus l E X).reduction.map
        ((pullbackTensorIntegralTensorModel l E X).hom.app (M.obj, K.obj))),
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun k ↦
      (pullbackTensorCalculus l E X).reduction.map
        ((pullbackTensorIntegralTensorModel l E X).hom.app (K.obj, M.obj)) ≫ k)
      ((pullbackTensorCalculus l E X).adjunction.counit.naturality _)
  have h := (pullbackTensorIntegralBraiding_existsUnique l E X K M).unique
    ((pullbackTensorIntegralBraiding_existsUnique l E X K M).exists.choose_spec) he
  exact congrArg (fun i ↦ i.hom.hom) h

/-- The completion-conjugated symmetry of a normalized datum is the canonical
integral Koszul braiding on constructible completed tensors.

Source: Stacks 06YL and 08J9; blueprint thm-coef-rational-verdier, paragraph 3.
Proof: choose flat-term K-flat representatives of the two inputs. The representative
formula in `SignedSymmetry` is the homogeneous Koszul swap, and the canonical
`pullbackTensorIntegralBraiding` has the same representative formula. The
representative equation of the completion map transports both maps to the same
completed tensor chain map. Naturality of the supplied symmetry transports the
identity from representatives to the constructible objects.
(blueprint: new-lem-coef-rational-verdier-completed-interchange-canonical). -/
theorem completedInterchange_eq_integralBraiding
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : Datum D l hl X E w)
    (hA : ∀ (K M K' M' : IntegralHom.Derived.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (f : K ⟶ K') (g : M ⟶ M'),
      A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' M').hom =
        (A.symmetry.swap K M).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f))
    (K M : sfIntegralConstructibleCategory l E X) :
    completedInterchange D l hl X E w A K M =
      (pullbackTensorIntegralBraiding l E X (hW := units D l hl X) K M).hom := by
  let sw : A.ordinary.tensor ⟶ pullbackTensorSwap _ ⋙ A.ordinary.tensor :=
    { app := fun KM ↦ (A.symmetry.swap KM.1 KM.2).hom
      naturality := fun {KM KM'} f ↦ hA _ _ _ _ f.1 f.2 }
  let left := sw ≫ Functor.whiskerLeft (pullbackTensorSwap _ ) A.completion.map
  let right := A.completion.map ≫ (completedSignedSwap l E X).hom
  have heq : left = right := by
    let q := integralOperationsGoodLocalization l E X
    let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E X
    apply Localization.natTrans_ext (q.prod q) (V.prod V)
    rintro ⟨P, Q⟩
    obtain ⟨s, hs, hswap⟩ := A.symmetry.representative P.obj Q.obj
      P.property.1 Q.property.1
    have hcPQ := eq_of_heq (A.completion.representative P Q)
    have hcQP := eq_of_heq (A.completion.representative Q P)
    have hchain := completion_signed_representative D l hl X E P Q s hs
    change (A.symmetry.swap (DerivedCategory.Q.obj P.obj)
        (DerivedCategory.Q.obj Q.obj)).hom ≫
          A.completion.map.app (DerivedCategory.Q.obj Q.obj, DerivedCategory.Q.obj P.obj) =
      A.completion.map.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (completedSignedSwap l E X).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
    apply (cancel_epi (A.ordinary.representative.hom.app
      (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩))).1
    apply (cancel_mono ((integralCompletedTensorComparison l E X).hom.app (Q, P))).1
    rw [← hswap]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [hcQP, hchain, ← hcPQ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have h := congrArg (fun t ↦ t.app (K.obj, M.obj)) heq
  change (A.symmetry.swap K.obj M.obj).hom ≫ A.completion.map.app (M.obj, K.obj) =
    A.completion.map.app (K.obj, M.obj) ≫
      (completedSignedSwap l E X).hom.app (K.obj, M.obj) at h
  apply ObjectProperty.hom_ext
  dsimp only [completedInterchange, ObjectProperty.homMk_hom]
  rw [canonical_normalization D l hl X E K M]
  rw [h]
  exact (@asIso _ _ _ _ (A.completion.map.app (K.obj, M.obj))
    (A.completion.invertible K M)).inv_hom_id_assoc _

end WeilConjectures.RationalVerdier
