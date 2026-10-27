/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.PointTransportStrictQuotientModels
import Sheaf.Paper.PointTransportStrictQuotientIdentities
import Sheaf.Paper.PointTransportStrictQuotientFiniteEvaluation
import all Sheaf.Paper.IntegralOperationsWellDefined
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Strict point transport on simultaneous quotient complexes

The strict identities assemble into functors to complexes of towers and descend
uniquely through the localization of flat-term K-flat complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem coefficient_square (n : ℕ) :
    inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
      (isoSectionwiseInverseImage (frobeniusPointIso D).hom RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
        inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n := by
  exact limit.lift_π _ _

/-- Strict quotient, augmentation and chain-map identities, followed by coherent
localization descent and the prescribed finite point-transport evaluations.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3) (blueprint: lem-trf-point-transport-strict-quotient).

Proof: the degreewise section formula gives the strict transition, augmentation
and chain-map identities by restriction and adjunction-unit naturality. The two
published pure-tensor formulas give the theta clause. Naturality of exact-functor
localization factors identifies every finite evaluation with the specified finite
transport. Reorder towers of complexes as complexes of towers; K-flat reduction
and exact pullback, scalar restriction and sections preserve quasi-isomorphisms
levelwise. Finally lift the two functors and their natural transformation through
the existing good-complex localization. Localization extensionality gives uniqueness. -/
theorem pointTransport_strictQuotient (hl : l ≠ D.p) :
    (∀ n : ℕ,
      inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom ≫
          limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
        (isoSectionwiseInverseImage (frobeniusPointIso D).hom RingCat.{u + 1}).map
            (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
          inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P.obj) ≫
          strictQuotientPointMap D l E n P.obj =
        strictQuotientPointMap D l E (n + 1) P.obj ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            ((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P.obj)) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n) ≫
          strictQuotientPointMap D l E n P.obj =
        frobeniusPointIntegralSigma D l E P.obj ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj)) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ) (i : ℤ) (V : (Spec (.of D.k)).ProEt)
      (x : (P.obj.X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj V))),
      ((inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj).f i).val.app
          (op V) x =
        ((inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
          ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)).f i).val.app
            (op V)
            (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.obj.X i)
              (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj V)) 1 x)) ∧
    (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (f : P.obj ⟶ P'.obj) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).map f) ≫
          strictQuotientPointMap D l E n P'.obj =
        strictQuotientPointMap D l E n P.obj ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).map f)) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory),
      sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj) →
      ∀ n : ℕ,
        DerivedCategory.Q.map (strictQuotientPointMap D l E n P.obj) ≫
            (strictQuotientPointTargetIso D l E n
              ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)).hom =
          (strictQuotientPointSectionsIso D l E n
              ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)).hom ≫
            (strictQuotientPointDerivedRestriction l E n).map
              (frobeniusPointTransportFinite D l hl E n
                (DerivedCategory.Q.obj
                  ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)))) ∧
    ∃ (A B : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory ⥤
        CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ℤ)
      (eA : A ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
          (Functor.ofOpSequence (X := fun n ↦
            unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n)
            (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)))
      (eB : B ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
          integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)))
      (V : A ⟶ B),
      (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ),
        ((eA.inv.app P ≫ HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (V.app P) ≫ eB.hom.app P).app (op n)) = strictQuotientPointMap D l E n P.obj) ∧
      (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (f : P ⟶ P'), QuasiIso f.hom → QuasiIso (A.map f) ∧ QuasiIso (B.map f)) ∧
      ∃ (F H : DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
          DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
        (eF : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ F ≅
          A ⋙ DerivedCategory.Q)
        (eH : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ H ≅
          B ⋙ DerivedCategory.Q),
        ∃! τ : F ⟶ H,
          ∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
            τ.app (DerivedCategory.Q.obj P.obj) ≫ eH.hom.app P =
              eF.hom.app P ≫ DerivedCategory.Q.map (V.app P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact coefficient_square D l E n
  · intro P n
    exact (strictQuotientPointMap_identities D l E).1 P.obj n
  · intro P n
    exact (strictQuotientPointMap_identities D l E).2.1 P.obj n
  · intro P n i V x
    have hθ := (inverseImageReductionTheta_existsUnique l E (frobeniusPointIso D).hom
      n P.obj).exists.choose_spec i V x
    have hκ := (inverseImageFiniteComparison_existsUnique l E (frobeniusPointIso D).hom
      n ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)
      ).exists.choose_spec i V
        (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.obj.X i)
          (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj V)) 1 x)
    exact hθ.trans hκ.symm
  · intro P P' f n
    exact (strictQuotientPointMap_identities D l E).2.2 P.obj P'.obj f n
  · intro P _ n
    exact strictQuotientPointMap_derived D l E hl n P.obj
  · let C := (integralOperationsGoodComplex l E (Spec (.of D.k)))
    let S := (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)
    let DA := C.ι ⋙
      (Functor.ofOpSequence
        (X := fun n ↦ unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n)
        (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
        (Functor.whiskeringRight _ _ _).obj S
    let DB := C.ι ⋙ integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
      (Functor.whiskeringRight _ _ _).obj S
    let e := HomologicalComplex.functorEquivalence
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
      (.up ℤ) ℕᵒᵖ
    let A := DA ⋙ e.inverse
    let B := DB ⋙ e.inverse
    let eA : A ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ DA := Iso.refl _
    let eB : B ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ DB := Iso.refl _
    let v : DA ⟶ DB :=
      { app P := NatTrans.ofOpSequence (fun n ↦ strictQuotientPointMap D l E n P.obj)
          (fun n ↦ by
            dsimp only [DA, DB, Functor.comp_obj, Functor.comp_map,
              Functor.flip_obj_map, Functor.whiskeringRight_obj_obj,
              integralOperationsPullbackTowerFunctor]
            simp only [Functor.ofOpSequence_map_homOfLE_succ]
            exact (strictQuotientPointMap_identities D l E).1 P.obj n)
        naturality P P' f := by
          apply NatTrans.ext
          funext n
          exact (strictQuotientPointMap_identities D l E).2.2 P.obj P'.obj f.hom n.unop }
    let V : A ⟶ B := Functor.whiskerRight v e.inverse
    have hq (P P' : C.FullSubcategory) (f : P ⟶ P') (hf : QuasiIso f.hom) :
        QuasiIso (A.map f) ∧ QuasiIso (B.map f) := by
      have hred (n : ℕ) :
          QuasiIso ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).map f.hom) :=
        finiteReduction_quasiIso l E (Spec (.of D.k)) n f.hom P.property P'.property hf
      constructor
      · apply (HomologicalComplex.quasiIso_iff_evaluation _).2
        intro n
        let R := scalarReductionRestriction l E (Spec (.of D.k)) n.unop
        have hR := HomologicalComplex.quasiIso_map_of_preservesHomology _ R
          (hφ := hred n.unop)
        exact HomologicalComplex.quasiIso_map_of_preservesHomology _
          (pointIntegralSections l E D.k) (hφ := hR)
      · apply (HomologicalComplex.quasiIso_iff_evaluation _).2
        intro n
        let T := integralOperationsLevelPullback l E (frobeniusPointIso D).hom n.unop
        have he := Scheme.coefficientProEtaleModulePullback_exact.{u, u}
          (frobeniusPointIso D).hom
          (CommRingCat.of (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n.unop + 1))))
        let : PreservesFiniteLimits T := he.1
        let : PreservesFiniteColimits T := he.2
        have hT := HomologicalComplex.quasiIso_map_of_preservesHomology _ T
          (hφ := hred n.unop)
        let R := scalarReductionRestriction l E (Spec (.of D.k)) n.unop
        have hR := HomologicalComplex.quasiIso_map_of_preservesHomology _ R (hφ := hT)
        exact HomologicalComplex.quasiIso_map_of_preservesHomology _
          (pointIntegralSections l E D.k) (hφ := hR)
    refine ⟨A, B, eA, eB, V, ?_, hq, ?_⟩
    · intro P n
      rfl
    · let L := integralOperationsGoodLocalization l E (Spec (.of D.k))
      let W := (HomologicalComplex.quasiIso (integralTowerModules l E (Spec (.of D.k)))
        (.up ℤ)).inverseImage C.ι
      let : L.IsLocalization W :=
        integralOperationsGoodLocalization_isLocalization l E (Spec (.of D.k))
      have hA : W.IsInvertedBy (A ⋙ DerivedCategory.Q) := by
        intro P P' f hf
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ (A.map f)).2
          (hq P P' f hf).1
      have hB : W.IsInvertedBy (B ⋙ DerivedCategory.Q) := by
        intro P P' f hf
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ (B.map f)).2
          (hq P P' f hf).2
      let F := Localization.lift (A ⋙ DerivedCategory.Q) hA L
      let H := Localization.lift (B ⋙ DerivedCategory.Q) hB L
      let eF := Localization.fac (A ⋙ DerivedCategory.Q) hA L
      let eH := Localization.fac (B ⋙ DerivedCategory.Q) hB L
      let τ := Localization.liftNatTrans L W (A ⋙ DerivedCategory.Q)
        (B ⋙ DerivedCategory.Q) F H (Functor.whiskerRight V DerivedCategory.Q)
      have hτ (P : C.FullSubcategory) :
          τ.app (DerivedCategory.Q.obj P.obj) ≫ eH.hom.app P =
            eF.hom.app P ≫ DerivedCategory.Q.map (V.app P) := by
        change τ.app (L.obj P) ≫ eH.hom.app P = _
        dsimp only [τ]
        rw [Localization.liftNatTrans_app]
        simp only [Category.assoc, Functor.whiskerRight_app]
        change eF.hom.app P ≫ DerivedCategory.Q.map (V.app P) ≫
          eH.inv.app P ≫ eH.hom.app P = _
        simp only [Iso.inv_hom_id_app]
        exact congrArg (fun t ↦ eF.hom.app P ≫ t)
          (Category.comp_id (DerivedCategory.Q.map (V.app P)))
      refine ⟨F, H, eF, eH, τ, hτ, ?_⟩
      intro τ' hτ'
      apply Localization.natTrans_ext L W
      intro P
      apply (cancel_mono (eH.hom.app P)).1
      exact (hτ' P).trans (hτ P).symm

end WeilConjectures
