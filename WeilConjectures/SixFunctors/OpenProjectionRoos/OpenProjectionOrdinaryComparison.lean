/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The ordinary open projection comparison

The derived open projection isomorphism `j_! K ⊗ P ≅ j_!(K ⊗ j^* P)` on the ordinary
(uncompleted) tensor models, normalized by the chain-level total tensor comparison on complexes
that are K-flat with flat terms (`ordinaryProjection_exists`).

## Implementation details

The chain-level comparison is localized: on pairs of good complexes, both sides are computed by
total tensor complexes through the representative isomorphisms of the tensor models and the
exact-functor factorizations, and good complexes localize to the derived category. The
comparison is the unique descent of the resulting natural isomorphism.

## References

* Stacks Project, Tags 0GL1, 09BP
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

section Ordinary

variable [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
  [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
  (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
  (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
  (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))

/-- Complexes with flat terms that are K-flat for the ordinary tensor. -/
abbrev flatComplexes (W : Scheme.{u}) :=
  proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W)

/-- Pairs of good complexes on the open and on the ambient scheme. -/
abbrev GoodPairs := (integralOperationsGoodComplex l E U).FullSubcategory ×
  (integralOperationsGoodComplex l E X).FullSubcategory

/-- The inclusion of pairs of good complexes. -/
abbrev goodPairs : GoodPairs l E (U := U) (X := X) ⥤
    CochainComplex (scalarReductionSource l E U) ℤ ×
      CochainComplex (scalarReductionSource l E X) ℤ :=
  (integralOperationsGoodComplex l E U).ι.prod (integralOperationsGoodComplex l E X).ι

/-- The localization of pairs of good complexes. -/
abbrev goodPairsLocalization :=
  (integralOperationsGoodLocalization l E U).prod (integralOperationsGoodLocalization l E X)

/-- The flat representatives `(j_! Q, F)` of a pair of good complexes. -/
abbrev leftRepresentatives : GoodPairs l E (U := U) (X := X) ⥤
    (flatComplexes l E X).FullSubcategory ×
    (flatComplexes l E X).FullSubcategory :=
  ((flatComplexes l E X).lift
      ((integralOperationsGoodComplex l E U).ι ⋙ OpenSemilinearTensor.extensionComplex l E j o)
      (fun Q ↦ flat X _ (extendGood Q.obj Q.property))).prod
    ((flatComplexes l E X).lift
      (integralOperationsGoodComplex l E X).ι (fun F ↦ flat X F.obj F.property))

/-- The flat representatives `(Q, j^* F)` of a pair of good complexes. -/
abbrev rightRepresentatives : GoodPairs l E (U := U) (X := X) ⥤
    (flatComplexes l E U).FullSubcategory ×
    (flatComplexes l E U).FullSubcategory :=
  ((flatComplexes l E U).lift
      (integralOperationsGoodComplex l E U).ι (fun Q ↦ flat U Q.obj Q.property)).prod
    ((flatComplexes l E U).lift
      ((integralOperationsGoodComplex l E X).ι ⋙ OpenSemilinearTensor.restrictionComplex l E j o)
      (fun F ↦ flat U _ (restrictGood F.obj F.property)))

/-- The chain-level open projection comparison on pairs of good complexes. -/
def goodChainComparison :
    goodPairs l E ⋙ (OpenSemilinearTensor.extensionComplex l E j o).prod (𝟭 _) ⋙
        OpenSemilinearTensor.total l E X ≅
      goodPairs l E ⋙ (𝟭 _).prod (OpenSemilinearTensor.restrictionComplex l E j o) ⋙
        OpenSemilinearTensor.total l E U ⋙ OpenSemilinearTensor.extensionComplex l E j o :=
  NatIso.ofComponents (fun K ↦ m.totalComparison.chain K.1.obj K.2.obj)
    (fun f ↦ m.totalComparison.naturality f.1.hom f.2.hom)

/-- The localized chain-level comparison on pairs of good complexes, computed through the
representative isomorphisms of both tensor models. -/
def goodProjectionComparison :
    goodPairsLocalization l E (U := U) (X := X) ⋙ leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
      goodPairsLocalization l E ⋙ rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙
        IntegralOpenReduction.shriek l E j o :=
  let ext := IntegralOpenReduction.extension l E j o
  let res := IntegralOpenReduction.restriction l E j o
  let β₁ : goodPairsLocalization l E (U := U) (X := X) ⋙ leftInputs l E j o ⋙
      q.tensorX.ordinary.tensor ≅
      leftRepresentatives l E j o flat extendGood ⋙
        (((flatComplexes l E X).ι ⋙ DerivedCategory.Q).prod
          ((flatComplexes l E X).ι ⋙ DerivedCategory.Q)) ⋙ q.tensorX.ordinary.tensor :=
    Functor.isoWhiskerRight (NatIso.prod
      (Functor.isoWhiskerLeft (integralOperationsGoodComplex l E U).ι
        ext.mapDerivedCategoryFactors)
        (Iso.refl (integralOperationsGoodLocalization l E X))) q.tensorX.ordinary.tensor
  let β₂ := Functor.isoWhiskerLeft (leftRepresentatives l E j o flat extendGood)
    q.tensorX.ordinary.representative.symm
  let β₃ : (goodPairs l E ⋙ (OpenSemilinearTensor.extensionComplex l E j o).prod (𝟭 _) ⋙
        OpenSemilinearTensor.total l E X) ⋙ DerivedCategory.Q ≅
      (goodPairs l E ⋙ (𝟭 _).prod (OpenSemilinearTensor.restrictionComplex l E j o) ⋙
        OpenSemilinearTensor.total l E U ⋙ OpenSemilinearTensor.extensionComplex l E j o) ⋙
          DerivedCategory.Q :=
    Functor.isoWhiskerRight (goodChainComparison l E j o SX SU AX AU st m) DerivedCategory.Q
  let β₄ : (goodPairs l E ⋙ (𝟭 _).prod (OpenSemilinearTensor.restrictionComplex l E j o) ⋙
        OpenSemilinearTensor.total l E U ⋙ OpenSemilinearTensor.extensionComplex l E j o) ⋙
          DerivedCategory.Q ≅
      (goodPairs l E ⋙ (𝟭 _).prod (OpenSemilinearTensor.restrictionComplex l E j o) ⋙
        OpenSemilinearTensor.total l E U ⋙ DerivedCategory.Q) ⋙
          IntegralOpenReduction.shriek l E j o :=
    Functor.isoWhiskerLeft (goodPairs l E ⋙ (𝟭 _).prod
      (OpenSemilinearTensor.restrictionComplex l E j o) ⋙ OpenSemilinearTensor.total l E U)
        ext.mapDerivedCategoryFactors.symm
  let β₅ := Functor.isoWhiskerRight (Functor.isoWhiskerLeft
    (rightRepresentatives l E j o flat restrictGood) q.tensorU.ordinary.representative)
      (IntegralOpenReduction.shriek l E j o)
  let β₆ : (rightRepresentatives l E j o flat restrictGood ⋙
        (((flatComplexes l E U).ι ⋙ DerivedCategory.Q).prod
          ((flatComplexes l E U).ι ⋙ DerivedCategory.Q)) ⋙ q.tensorU.ordinary.tensor) ⋙
          IntegralOpenReduction.shriek l E j o ≅
      goodPairsLocalization l E ⋙ rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙
        IntegralOpenReduction.shriek l E j o :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (NatIso.prod (Iso.refl (integralOperationsGoodLocalization l E U))
      (Functor.isoWhiskerLeft (integralOperationsGoodComplex l E X).ι
        res.mapDerivedCategoryFactors.symm)) q.tensorU.ordinary.tensor)
      (IntegralOpenReduction.shriek l E j o)
  β₁ ≪≫ β₂ ≪≫ β₃ ≪≫ β₄ ≪≫ β₅ ≪≫ β₆

private theorem cancel_isos {C : Type*} [Category C] {A B P D T F G : C}
    (t : A ≅ B) (r : P ≅ B) (x : P ⟶ D) (e : T ≅ D) (d : T ≅ F) (k : F ≅ G) :
    r.hom ≫ t.inv ≫ (t.hom ≫ r.inv ≫ x ≫ e.inv ≫ d.hom ≫ k.hom) ≫ k.inv ≫ d.inv ≫ e.hom = x := by
  simp

set_option backward.defeqAttrib.useBackward true in
/-- The ordinary open projection comparison, normalized by the chain-level comparison on
complexes that are K-flat with flat terms. -/
theorem ordinaryProjection_exists :
    ∃ (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
      rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o),
      OrdinaryRepresentative l E j o SX SU AX AU st m c q flat extendGood restrictGood
        ordinary := by
  have := integralOperationsGoodLocalization_isLocalization l E U
  have := integralOperationsGoodLocalization_isLocalization l E X
  let ff := Localization.fullyFaithfulWhiskeringLeft (goodPairsLocalization l E (U := U) (X := X))
    (((HomologicalComplex.quasiIso (integralTowerModules l E U) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E U).ι).prod
      ((HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E X).ι))
    (DerivedCategory (scalarReductionSource l E X))
  let α := goodProjectionComparison l E j o SX SU AX AU st m c q flat extendGood restrictGood
  refine ⟨ff.preimageIso α, ?_⟩
  intro Q F hQ hF
  have h : (ff.preimageIso α).hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj F) =
      α.hom.app (⟨Q, hQ⟩, ⟨F, hF⟩) :=
    congr_app (ff.map_preimage α.hom) (⟨Q, hQ⟩, ⟨F, hF⟩)
  apply heq_of_eq
  rw [h]
  exact cancel_isos
    (q.tensorX.ordinary.tensor.mapIso (Iso.prod
      ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app Q)
      (Iso.refl (DerivedCategory.Q.obj F))))
    (q.tensorX.ordinary.representative.app
      (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, flat X _ (extendGood Q hQ)⟩,
        ⟨F, flat X F hF⟩))
    (DerivedCategory.Q.map (m.totalComparison.chain Q F).hom)
    ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.app
      ((OpenSemilinearTensor.total l E U).obj
        (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
    ((IntegralOpenReduction.shriek l E j o).mapIso (q.tensorU.ordinary.representative.app
      (⟨Q, flat U Q hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
        flat U _ (restrictGood F hF)⟩)))
    ((IntegralOpenReduction.shriek l E j o).mapIso (q.tensorU.ordinary.tensor.mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj Q))
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.app F).symm)))

end Ordinary

end WeilConjectures.OpenProjectionRoos
