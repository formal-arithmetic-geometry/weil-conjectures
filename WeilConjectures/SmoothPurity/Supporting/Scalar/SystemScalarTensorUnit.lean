/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnitChain
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnitSquares
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData

/-! # Scalar extension preserves the unit of coherent systems

The derived scalar extension of coherent coefficient systems sends the tensor unit to the
tensor unit, compatibly with the normalized tensor comparison `derivedSigma` and both unitors.
Source: Stacks Project, Tags 07A4 and 0FPT.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open ScalarExtensionTower

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option maxHeartbeats 1000000 in
-- The two unitor squares unfold the representative tensor models on both sides.
/-- The derived scalar extension of coherent systems preserves the tensor unit, compatibly with
the normalized tensorator and both unitors.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: the unit is the coefficient ring in degree zero, a flat-term K-flat complex, and its
strict scalar extension is the coefficient ring of the larger field. On representatives the
right unitor descends scalar multiplication `x ⊗ a ↦ a • x`, and the strict scalar comparison
sends `x ⊗ a` to `x ⊗ a`; both routes give `a • x`. The left unitor is the right unitor composed
with the symmetry, which is compatible with the tensorator by `systemScalarTensorBraiding`. -/
theorem systemScalarTensorUnit
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃ e : (integralComparisonDerivedSequenceScalar l E L ι W).obj
        (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
        (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit,
      ∀ A : coefficientSequenceDerived l E W,
        (ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
            ((pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit, A) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom e.hom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj A))) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
            ((integralComparisonDerivedSequenceScalar l E L ι W).obj A)).hom =
        (integralComparisonDerivedSequenceScalar l E L ι W).map
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor A).hom ∧
        (ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
            (A, (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj A)) e.hom) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
            ((integralComparisonDerivedSequenceScalar l E L ι W).obj A)).hom =
        (integralComparisonDerivedSequenceScalar l E L ι W).map
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor A).hom := by
  let SE := pullbackTensorCalculus l E W
  let SL := pullbackTensorCalculus l L W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let C := scalar l E L ι W
  let δ := integralComparisonSequenceScalarModel l E L ι W
  let α := derivedSigma l E L ι W SE SL
  let UE := sequenceUnitComplex l E W
  let UL := sequenceUnitComplex l L W
  have hcoh (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] :
      ∃ β : @SymmetricCategory (coefficientSequenceDerived l F W) _
        (pullbackTensorCalculus l F W).systemClosed.monoidal,
        Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l F W)
          (pullbackTensorCalculus l F W).systemClosed
          (pullbackTensorCalculus l F W).systemTensorModel β) := by
    unfold pullbackTensorCalculus
    exact (coefficientDerivedSystemEvaluationCalculus l F W).choose_spec.some.systemTensorCoherence
  obtain ⟨_, ⟨KE⟩⟩ := hcoh E
  obtain ⟨_, ⟨KL⟩⟩ := hcoh L
  obtain ⟨c, hc⟩ := sequenceUnitComplexScalarIso_exists l E L ι W
  have hU : Good l E W UE := sequenceUnitComplex_good l E W
  have hεU : IsIso (δ.ε.app UE) := δ.computes _ hU.1
  let e : H.obj SE.systemClosed.monoidal.tensorUnit ≅ SL.systemClosed.monoidal.tensorUnit :=
    H.mapIso KE.unitIso ≪≫ @asIso _ _ _ _ (δ.ε.app UE) hεU ≪≫ DerivedCategory.Q.mapIso c ≪≫
      KL.unitIso.symm
  have res (X : coefficientSequenceDerived l E W) :
      ∃ P : Complex l E W, Good l E W P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let q := DerivedCategory.Q (C := coefficientSequenceModules l E W)
    obtain ⟨P, f, hP, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (q.objPreimage X)
    have : QuasiIso f := hf
    refine ⟨P, ⟨hP, fun n ↦ ?_⟩, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso X⟩⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E W) (P.X n)).symm (hflat n)
  have hα := (derivedSigma_existsUnique l E L ι W SE SL).exists.choose_spec
  change DerivedSigmaModel l E L ι W SE SL α at hα
  unfold DerivedSigmaModel at hα
  let _ := SE.systemClosed.monoidal
  let _ := SL.systemClosed.monoidal
  have hnat : MonoidalUnitorSquare.SigmaNatural H (fun X Y ↦ α.hom.app (X, Y)) :=
    fun f g ↦ α.hom.naturality (Prod.mkHom f g)
  refine ⟨e, fun A ↦ ?_⟩
  obtain ⟨P, hP, ⟨i⟩⟩ := res A
  have hεP : IsIso (δ.ε.app P) := δ.computes P hP.1
  constructor
  · refine MonoidalUnitorSquare.leftUnitor_square_of_iso H (fun X Y ↦ α.hom.app (X, Y)) hnat
      e.hom i ?_
    obtain ⟨hsU, hsP, hσ⟩ := hα UE P hU hP
    obtain ⟨lE, hlE, hlEm⟩ := KE.leftUnitor_model P hP.1
    obtain ⟨lL, hlL, hlLm⟩ := KL.leftUnitor_model (C.obj P) hsP.1
    have hstrict := scalarLeftUnitStrict l E L ι W c hc P lE.hom hlE lL.hom hlL
    have hn := KL.tensorIso_naturality (C.obj UE) (C.obj P) UL (C.obj P) (Or.inl hsU.1)
      (Or.inr hsP.1) c.hom (𝟙 _)
    rw [KL.tensorIso_both (C.obj UE) (C.obj P) hsU.1 hsP.1, DerivedCategory.Q.map_id] at hn
    have hlE' := KE.tensorIso_both UE P hU.1 hP.1
    have hstrict' := congrArg (fun f ↦ DerivedCategory.Q.map f) hstrict
    simp only [Functor.map_comp] at hstrict'
    erw [Functor.map_comp] at hstrict'
    exact MonoidalUnitorSquare.leftUnitor_square_of_models H (fun X Y ↦ α.hom.app (X, Y)) hnat
      KE.unitIso (SE.systemTensorModel.iso _ _ _ UE P hU.1 hP.1) (@asIso _ _ _ _ (δ.ε.app P) hεP)
      (δ.ε.app UE) (DerivedCategory.Q.map c.hom) KL.unitIso
      (SL.systemTensorModel.iso _ _ _ (C.obj UE) (C.obj P) hsU.1 hsP.1)
      (KL.tensorIso UL (C.obj P) (Or.inr hsP.1)) (δ.ε.app _)
      (DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app (UE, P)))
      (DerivedCategory.Q.map ((tensor l L W).map (Prod.mkHom c.hom (𝟙 _))))
      (DerivedCategory.Q.map lE.hom) (DerivedCategory.Q.map lL.hom)
      (DerivedCategory.Q.map (C.map lE.hom))
      hσ (hlE' ▸ hlEm) hlLm hn
      hstrict'
      (δ.ε.naturality lE.hom)
  · refine MonoidalUnitorSquare.rightUnitor_square_of_iso H (fun X Y ↦ α.hom.app (X, Y)) hnat
      e.hom i ?_
    obtain ⟨hsP, hsU, hσ⟩ := hα P UE hP hU
    obtain ⟨rE, hrE, hrEm⟩ := KE.rightUnitor_model P hP.1
    obtain ⟨rL, hrL, hrLm⟩ := KL.rightUnitor_model (C.obj P) hsP.1
    have hstrict := scalarRightUnitStrict l E L ι W c hc P rE.hom hrE rL.hom hrL
    have hn := KL.tensorIso_naturality (C.obj P) (C.obj UE) (C.obj P) UL (Or.inl hsP.1)
      (Or.inl hsP.1) (𝟙 _) c.hom
    rw [KL.tensorIso_both (C.obj P) (C.obj UE) hsP.1 hsU.1, DerivedCategory.Q.map_id] at hn
    have hrE' := KE.tensorIso_both P UE hP.1 hU.1
    have hstrict' := congrArg (fun f ↦ DerivedCategory.Q.map f) hstrict
    simp only [Functor.map_comp] at hstrict'
    erw [Functor.map_comp] at hstrict'
    exact MonoidalUnitorSquare.rightUnitor_square_of_models H (fun X Y ↦ α.hom.app (X, Y)) hnat
      KE.unitIso (SE.systemTensorModel.iso _ _ _ P UE hP.1 hU.1) (@asIso _ _ _ _ (δ.ε.app P) hεP)
      (δ.ε.app UE) (DerivedCategory.Q.map c.hom) KL.unitIso
      (SL.systemTensorModel.iso _ _ _ (C.obj P) (C.obj UE) hsP.1 hsU.1)
      (KL.tensorIso (C.obj P) UL (Or.inl hsP.1)) (δ.ε.app _)
      (DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app (P, UE)))
      (DerivedCategory.Q.map ((tensor l L W).map (Prod.mkHom (𝟙 _) c.hom)))
      (DerivedCategory.Q.map rE.hom) (DerivedCategory.Q.map rL.hom)
      (DerivedCategory.Q.map (C.map rE.hom))
      hσ (hrE' ▸ hrEm) hrLm hn hstrict' (δ.ε.naturality rE.hom)

end WeilConjectures
