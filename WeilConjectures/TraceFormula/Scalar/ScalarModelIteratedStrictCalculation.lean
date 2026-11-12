/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLift
import WeilConjectures.TraceFormula.Scalar.ScalarTensorRoosCoordinates
import WeilConjectures.TraceFormula.Scalar.ScalarPresentationKFlat

/-! # Strict calculation of the iterated scalar realization

Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7;
Stacks Project, Tags 06YY and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

/-- Assemble five identities without unfolding any of the concrete functors. -/
private theorem assemble_calculation
    {V : Type*} [Category V]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₂ Y₃ Y₄ Z₀ Z₁ Z₂ W₀ W₁ H J : V}
    {p : X₀ ⟶ X₁} {u : X₁ ⟶ X₂} {v : X₂ ⟶ X₃} {w : X₃ ⟶ X₄}
    {x : X₄ ⟶ X₅} {y : X₅ ⟶ X₆}
    {u' : X₁ ⟶ Y₂} {v' : Y₂ ⟶ Y₃} {w' : Y₃ ⟶ X₄}
    {x' : Y₃ ⟶ Y₄} {z : Y₄ ⟶ X₅}
    {c : X₀ ⟶ W₀} {d : W₀ ⟶ W₁} {e : W₁ ⟶ Z₀}
    {n : Z₀ ⟶ Z₁} {o : Z₁ ⟶ Z₂} {r : Z₂ ⟶ Y₂}
    {c' : W₀ ⟶ H} {g : H ⟶ Y₄} {a : H ⟶ J} {b : J ⟶ X₆}
    (hsuffix : u ≫ v ≫ w = u' ≫ v' ≫ w')
    (hbridge : w' ≫ x = x' ≫ z)
    (hprefix : p ≫ u' = c ≫ d ≫ e ≫ n ≫ o ≫ r)
    (hzero : d ≫ e ≫ n ≫ o ≫ r ≫ v' ≫ x' = c' ≫ g)
    (htail : g ≫ z ≫ y = a ≫ b) :
    (p ≫ u) ≫ v ≫ w ≫ x ≫ y = c ≫ c' ≫ a ≫ b := by
  calc
    (p ≫ u) ≫ v ≫ w ≫ x ≫ y = p ≫ (u ≫ v ≫ w) ≫ x ≫ y := by
      simp only [Category.assoc]
    _ = p ≫ (u' ≫ v' ≫ w') ≫ x ≫ y := by rw [hsuffix]
    _ = (p ≫ u') ≫ v' ≫ (w' ≫ x) ≫ y := by simp only [Category.assoc]
    _ = (c ≫ d ≫ e ≫ n ≫ o ≫ r) ≫ v' ≫ (x' ≫ z) ≫ y := by
      rw [hprefix, hbridge]
    _ = c ≫ (d ≫ e ≫ n ≫ o ≫ r ≫ v' ≫ x') ≫ z ≫ y := by
      simp only [Category.assoc]
    _ = c ≫ (c' ≫ g) ≫ z ≫ y := by rw [hzero]
    _ = c ≫ c' ≫ (g ≫ z ≫ y) := by simp only [Category.assoc]
    _ = c ≫ c' ≫ a ≫ b := by rw [htail]

attribute [local irreducible] integralComparisonSequenceScalarModel
  coefficientSequenceRestriction coefficientConstantTowerLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F)
  (X : Scheme.{u})

set_option maxHeartbeats 1200000 in
-- Elaborating the transported coefficient and derived-category instances needs extra heartbeats.
/-- The iterated route, on one simultaneous presentation, is the localized ordinary
scalar counits followed by the strict tensor associator and quotient augmentation.
It does not involve a direct scalar realization model or a derived associator.

Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7;
Stacks 06YY and 0941; steps 1--3 of lem-trf-scalar-model-associativity.
(blueprint: lem-trf-scalar-model-iterated-strict-calculation).

The presentation is required to be coherent with the whole-system adjunction.
This requirement fixes its realization before taking the total limit; equality
only after separate finite derived evaluations does not fix that realization.

Proof in words: normalize bEL on the given coherent presentation C,e,kappa and choose
its normalized tower isomorphism qEL. The completed scalar comparison formula
identifies the first realization, followed by the presentation map, with the
ordinary E-to-L counit and the strict augmentation transported through qEL.
The theorem scalarPresentationKFlat makes C K-flat from its finite evaluation
isomorphisms. Normalize the derived system associator at C and use its
naturality at e: its three-factor suffix becomes the L-to-F image of the first
presentation map, the universal scalar cochain counit, and the strict system
associator. Move the first presentation map across the actual SL adjunction
counit, bLF.realization, and the second completed comparison by naturality.
The theorem scalarTensorRoosCoordinates computes the transported first and
direct augmentations: both have zero shifted coordinates, and the second has
the nested pure-tensor coordinates of the scalar extension of the first.
Apply scalarModelRoosZeroLift to this pair. Naturality of the normalized Roos
bridge moves the strict system associator past the limit. Cancel it and q
against their inverses in the transported direct augmentation. The result is
exactly the two ordinary scalar counits followed by the ordinary sheaf tensor
associator and direct augmentation. These are whole-system identities; no
faithfulness of separate derived evaluations or inverse completion map is used.
The same argument includes zero complexes and repeated coefficient fields. -/
theorem scalarModelIteratedStrictCalculation
    (SE : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (bEL : IntegralComparisonScalarModel l E L ι X SE ρL)
    (bLF : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj)
    (hC : CoefficientReductionPresentation l E X SE.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ)
    (hcoh : IsIntegralComparisonPresentationCoherent l E X SE P.obj C e κ)
    (q : (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E F (j.comp ι) X).obj P.obj)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l F X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l F X
            ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E F (j.comp ι) X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E F (j.comp ι) X n (P.obj.X i) U s x) :
    ((completedDerivedScalarExtension l L F j X).map
        ((completedScalarComparison l E L ι X).app (DerivedCategory.Q.obj P.obj)) ≫
      (completedScalarComparison l L F j X).app
        ((integralScalarExtensionOfUniverses l E L ι X).obj (DerivedCategory.Q.obj P.obj)) ≫
      (integralScalarExtensionOfUniverses l L F j X).map
        (bEL.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
      bLF.realization.hom.app
        ((coefficientSequenceLimit l L X).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj (DerivedCategory.Q.obj P.obj))))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSystemScalarComposition l E L F ι j X).hom.app
          (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l E F (j.comp ι) X).map e.hom) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).ε.app C) ≫
      (integralComparisonRoosBridge l F X ρF _).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
    (completedDerivedScalarExtension l L F j X).map
        (completedScalarCounit l E L ι X P.obj) ≫
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫
      DerivedCategory.Q.map
        ((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
          (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P.obj) ≫
      DerivedCategory.Q.map
        ((completedScalarChainComparison l E F (j.comp ι) X).app P.obj) := by
  let B := completedDerivedScalarExtension l L F j X
  let A := integralComparisonDerivedSequenceScalar l E L ι X
  let A' := integralComparisonDerivedSequenceScalar l L F j X
  let A'' := integralComparisonDerivedSequenceScalar l E F (j.comp ι) X
  let T := coefficientSequenceLimit l F X
  let TL := coefficientSequenceLimit l L X
  let M := integralComparisonSequenceScalarModel l E L ι X
  let M' := integralComparisonSequenceScalarModel l L F j X
  let M'' := integralComparisonSequenceScalarModel l E F (j.comp ι) X
  let K := DerivedCategory.Q.obj P.obj
  let N := A.obj (SE.reduction.obj K)
  let D := (M.E.mapHomologicalComplex (.up ℤ)).obj C
  let a := (NatIso.mapHomologicalComplex
    (integralComparisonSequenceScalarComposition l E L ι F j X) (.up ℤ)).app C
  let w := ((coefficientSequenceRestriction l F X).mapHomologicalComplex
    (.up ℤ)).mapIso a
  let wa := HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso w
  let v := A.map e.hom ≫ M.ε.app C
  obtain ⟨qEL, hqEL, hnEL⟩ := bEL.normalization P C e κ hC hcoh
  let f := (completedScalarChainComparison l E L ι X).app P.obj ≫
    integralOperationsRoosFunctor.map qEL.inv
  let g := (CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
      (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P.obj ≫
    (completedScalarChainComparison l E F (j.comp ι) X).app P.obj ≫
    integralOperationsRoosFunctor.map (q.inv ≫ wa.inv)
  have hcoords := scalarTensorRoosCoordinates l E L F ι j X P.obj C κ qEL hqEL q hq
  change (∀ i, _) ∧ (∀ i, _) ∧ _ at hcoords
  obtain ⟨hf, hg, hfg⟩ := hcoords
  have hzero := scalarModelRoosZeroLift l E L F ι j X SL ρL ρF bLF P D f g hf hg hfg
  have hfirst : (completedScalarComparison l E L ι X).app K ≫
      bEL.realization.hom.app K ≫ TL.map v =
      completedScalarCounit l E L ι X P.obj ≫
        DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv := by
    have hc := (completedScalarComparison_existsUnique l E L ι X).exists.choose_spec P
    change (completedScalarComparison l E L ι X).app K ≫
      (integralScalarExtensionComparisonOfUniverses l E L ι X).hom.app P = _ at hc
    have hn := congrArg (fun z ↦ (completedScalarComparison l E L ι X).app K ≫ z ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map qEL.inv) ≫
      (integralComparisonRoosBridge l L X ρL D).inv) hnEL
    rw [reassoc_of% hc] at hn
    have hcancel := Iso.hom_inv_id_map qEL
      (integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    simp only [Functor.comp_map] at hcancel
    simp only [Category.assoc] at hn
    erw [reassoc_of% hcancel] at hn
    erw [Iso.hom_inv_id, Category.comp_id] at hn
    simpa only [v, f, M, TL, Functor.map_comp, Category.assoc] using hn
  have hK := scalarPresentationKFlat l E X P C κ
  have ha :=
    (integralComparisonSystemScalarComposition_existsUnique l E L F ι j X).exists.choose_spec
      C hK
  change (integralComparisonSystemScalarComposition l E L F ι j X).hom.app
      (DerivedCategory.Q.obj C) ≫ M''.ε.app C =
    A'.map (M.ε.app C) ≫ M'.ε.app D ≫ DerivedCategory.Q.map a.hom at ha
  have hbridge : T.map (DerivedCategory.Q.map a.hom) ≫
      (integralComparisonRoosBridge l F X ρF _).hom =
    (integralComparisonRoosBridge l F X ρF _).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map wa.hom) := by
    dsimp only [T, coefficientSequenceLimit, integralComparisonRoosBridge]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Category.assoc]
    erw [← Functor.map_comp_assoc, Functor.mapDerivedCategoryFactors_hom_naturality,
      Functor.map_comp, Category.assoc, ρF.comparison.hom.naturality]
    rfl
  have hsuffix :
      (integralComparisonSystemScalarComposition l E L F ι j X).hom.app
          (SE.reduction.obj K) ≫ A''.map e.hom ≫ M''.ε.app C =
        A'.map v ≫ M'.ε.app D ≫ DerivedCategory.Q.map a.hom := by
    rw [← Category.assoc,
      ← (integralComparisonSystemScalarComposition l E L F ι j X).hom.naturality]
    rw [Category.assoc, ha]
    simp only [v, Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  have hmove :
      B.map ((completedScalarComparison l E L ι X).app K) ≫
        (completedScalarComparison l L F j X).app
          ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
        (integralScalarExtensionOfUniverses l L F j X).map
          (bEL.realization.hom.app K) ≫ bLF.realization.hom.app (TL.obj N) ≫
        T.map (A'.map (SL.adjunction.counit.app N)) ≫ T.map (A'.map v) =
      B.map ((completedScalarComparison l E L ι X).app K ≫
        bEL.realization.hom.app K ≫ TL.map v) ≫
        (completedScalarComparison l L F j X).app (TL.obj (DerivedCategory.Q.obj D)) ≫
        bLF.realization.hom.app (TL.obj (DerivedCategory.Q.obj D)) ≫
        T.map (A'.map (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) := by
    rw [← (completedScalarComparison l L F j X).naturality_assoc]
    have hcounit := SL.adjunction.counit.naturality v
    change SL.reduction.map (TL.map v) ≫
        SL.adjunction.counit.app (DerivedCategory.Q.obj D) =
      SL.adjunction.counit.app N ≫ v at hcounit
    rw [← T.map_comp, ← A'.map_comp, ← hcounit]
    simp only [Functor.map_comp, Category.assoc]
    have hb := bLF.realization.hom.naturality (TL.map v)
    change (integralScalarExtensionOfUniverses l L F j X).map (TL.map v) ≫
        bLF.realization.hom.app (TL.obj (DerivedCategory.Q.obj D)) =
      bLF.realization.hom.app (TL.obj N) ≫ T.map (A'.map (SL.reduction.map (TL.map v))) at hb
    erw [← reassoc_of% hb]
    have hx := (completedScalarComparison l L F j X).naturality (TL.map v)
    change B.map (TL.map v) ≫
        (completedScalarComparison l L F j X).app (TL.obj (DerivedCategory.Q.obj D)) =
      (completedScalarComparison l L F j X).app (TL.obj N) ≫
        (integralScalarExtensionOfUniverses l L F j X).map (TL.map v) at hx
    erw [← reassoc_of% hx]
  have htail : DerivedCategory.Q.map g ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map wa.hom) ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
    DerivedCategory.Q.map
      ((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
        (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P.obj) ≫
      DerivedCategory.Q.map
        ((completedScalarChainComparison l E F (j.comp ι) X).app P.obj) := by
    have hwcancel := Iso.inv_hom_id_map wa
      (integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    have hqcancel := Iso.inv_hom_id_map q
      (integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    simp only [Functor.comp_map] at hwcancel hqcancel
    simp only [g, Functor.map_comp, Category.assoc]
    erw [reassoc_of% hwcancel, hqcancel]
    erw [Category.comp_id]
  simp only [Functor.map_comp, Category.assoc] at hzero
  have hsuffixMap := congrArg (fun z ↦ T.map z) hsuffix
  simp only [Functor.map_comp] at hsuffixMap
  let pref := B.map ((completedScalarComparison l E L ι X).app K) ≫
    (completedScalarComparison l L F j X).app
      ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
    (integralScalarExtensionOfUniverses l L F j X).map
      (bEL.realization.hom.app K) ≫ bLF.realization.hom.app (TL.obj N) ≫
    T.map (A'.map (SL.adjunction.counit.app N))
  rw [hfirst, B.map_comp, B.map_comp] at hmove
  have hprefix : pref ≫ T.map (A'.map v) =
      B.map (completedScalarCounit l E L ι X P.obj) ≫
        B.map (DerivedCategory.Q.map f) ≫
        B.map (integralComparisonRoosBridge l L X ρL D).inv ≫
        (completedScalarComparison l L F j X).app (TL.obj (DerivedCategory.Q.obj D)) ≫
        bLF.realization.hom.app (TL.obj (DerivedCategory.Q.obj D)) ≫
        T.map (A'.map (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) := by
    simpa only [pref, Category.assoc] using hmove
  simpa only [pref, Category.assoc] using
    assemble_calculation hsuffixMap hbridge hprefix hzero htail

end WeilConjectures
