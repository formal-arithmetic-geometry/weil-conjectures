/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Y3 and H8
-/
module

public import Sheaf.Paper.CompletedComparisonQuotientRealizationDefs
import all Sheaf.Paper.CompletedComparisonQuotientRealizationDefs
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Paper.CompletedQuotientReductionPresentation
import all Sheaf.Paper.QuotientExpressionStrictKFlatTowers
import Sheaf.Paper.QuotientExpressionKFlatOperations
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] pullbackTensorReferenceTensor
  pullbackTensorReferencePullback integralOperationsGoodLocalization
  value expression IntegralCoherence.value coefficientSequenceInternalHom Pi.eval
attribute [local implicit_reducible] substituteInputs strictMap

private theorem quotient_good {Y : Scheme.{u}}
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    StrictQuotient.SystemGood l E (quotient l E P.obj) := by
  apply (StrictQuotient.levelwiseFlatModels l E Y _).1
  intro n
  let e := ((pullbackTensorReductionEvaluationComplex l E Y n).app P.obj).symm
  constructor
  · exact SheafOfModules.kFlat_iso_independent
      (integralCoefficientCommRingSheaf l E Y n) e.symm
      ((coefficientTensorModelPreservation l E Y).1 P.obj P.property.1 n)
  · intro k
    exact SheafOfModules.flatOnSite_of_iso (integralCoefficientCommRingSheaf l E Y n)
      ((HomologicalComplex.eval _ _ k).mapIso e).symm
      (StrictQuotient.reduction_flat l E Y P.obj P.property.1 P.property.2 n k)

private theorem expressions_good {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory) :
    GoodExpressions l E h f P := by
  intro W A
  induction A with
  | input i => exact quotient_good l E (P i)
  | unitY => exact StrictQuotient.unit_system_good l E Y
  | unitX => exact StrictQuotient.unit_system_good l E X
  | unitZ => exact StrictQuotient.unit_system_good l E Z
  | tensor A B hA hB => exact StrictQuotient.tensor_system_good l E _ _ hA hB
  | pullF A hA => exact StrictQuotient.pull_system_good l E f _ hA
  | pullH A hA => exact StrictQuotient.pull_system_good l E h _ hA
  | pullHF A hA => exact StrictQuotient.pull_system_good l E (h ≫ f) _ hA

private theorem expressions_generated {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (N : Fin 3 → StrictQuotient.Complex l E Y) {W : Scheme.{u}}
    (A : StrictQuotient.Expression h f 3 W) :
    StrictQuotient.Generated l E h f N W (strictValue l E N A) := by
  induction A with
  | input i => exact .input i
  | unitY => exact .unitY
  | unitX => exact .unitX
  | unitZ => exact .unitZ
  | tensor A B hA hB => exact .tensor hA hB
  | pullF A hA => exact .pullF hA
  | pullH A hA => exact .pullH hA
  | pullHF A hA => exact .pullHF hA

private theorem generated_good {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (W : Scheme.{u}) (K : StrictQuotient.Complex l E W)
    (hK : StrictQuotient.Generated l E h f (fun i ↦ quotient l E (P i).obj) W K) :
    ∀ n, StrictQuotient.Good l E K n := by
  apply (StrictQuotient.levelwiseFlatModels l E W K).2
  induction hK with
  | input i => exact quotient_good l E (P i)
  | unitY => exact StrictQuotient.unit_system_good l E Y
  | unitX => exact StrictQuotient.unit_system_good l E X
  | unitZ => exact StrictQuotient.unit_system_good l E Z
  | tensor hA hB hA' hB' => exact StrictQuotient.tensor_system_good l E _ _ hA' hB'
  | pullF hA hA' => exact StrictQuotient.pull_system_good l E f _ hA'
  | pullH hA hA' => exact StrictQuotient.pull_system_good l E h _ hA'
  | pullHF hA hA' => exact StrictQuotient.pull_system_good l E (h ≫ f) _ hA'

private theorem expressions_normalized {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hpres : ∀ i : Fin 3, CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      (P i).obj (P i).property.1 (quotient l E (P i).obj)
      ((pullbackTensorReductionModel l E Y).app (P i))
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsNormalizedCoefficientSequence l E W
      (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) := by
  let N := fun i ↦ quotient l E (P i).obj
  let κ := fun i n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm
  have hκ : ∀ (i : Fin 3) {m n : ℕ} (hmn : n ≤ m),
      StrictQuotient.transition l E (N i) hmn ≫
          ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
            (κ i n).hom =
        (κ i m).hom ≫ (NatTrans.mapHomologicalComplex
          (coefficientOrdinaryQuotient l E Y hmn) (.up ℤ)).app (P i).obj := by
    intro i m n hmn
    exact (hpres i).2 m n hmn
  intro m n
  exact ((StrictQuotient.quotientExpressionKFlatOperations l E h f 3 N
    (fun i ↦ (P i).obj) κ hκ (generated_good l E h f P)).1 W _
      (expressions_generated l E h f N A)).1

private theorem counit_iso {W : Scheme.{u}} (A : coefficientSequenceDerived l E W)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsIso ((pullbackTensorCalculus l E W).adjunction.counit.app A) :=
  ((purNormalizedReconstructionOfScheme l E W (pullbackTensorCalculus l E W)).1 A hA).2

private theorem reduction_iso {W : Scheme.{u}}
    {K : DerivedCategory (scalarReductionSource l E W)}
    {A : coefficientSequenceDerived l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj A)
    [IsIso β] (hA : IsNormalizedCoefficientSequence l E W A) :
    IsIso (reduction l E β) := by
  have := counit_iso l E A hA
  unfold reduction
  infer_instance

private theorem tensor_substitution_iso {W : Scheme.{u}}
    {K H : DerivedCategory (scalarReductionSource l E W)}
    (A B : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (βA : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (βB : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B))
    [IsIso βA] [IsIso βB]
    (hnA : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A))
    (hnB : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj B)) :
    IsIso (tensorSubstitution l E A B hA hB βA βB) := by
  have := reduction_iso l E βA hnA
  have := reduction_iso l E βB hnB
  have : IsIso (Prod.mkHom (reduction l E βA) (reduction l E βB)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  unfold tensorSubstitution
  infer_instance

private theorem pull_substitution_iso {V W : Scheme.{u}} (g : V ⟶ W)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W)
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    [IsIso β] (hnA : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A)) :
    IsIso (pullSubstitution l E g A β) := by
  have := reduction_iso l E β hnA
  let e := ((pullbackTensorIntegralPullbackModel l E g).app K) ≪≫
    (coefficientSequenceLimit l E V).mapIso
      ((pullbackTensorSequenceDerived l E g).mapIso (asIso (reduction l E β))) ≪≫
    (coefficientSequenceLimit l E V).mapIso
      (((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.app A) ≪≫
        DerivedCategory.Q.mapIso ((pullBridge l E g).app A))
  unfold pullSubstitution
  change IsIso e.hom
  infer_instance

private theorem substitute_inputs_iso {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (N : Fin 3 → StrictQuotient.Complex l E Y)
    (M : Fin 3 → DerivedCategory (scalarReductionSource l E Y))
    (β : ∀ i : Fin 3, M i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N i)))
    (good : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l E (strictValue l E N A))
    (hn : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj (strictValue l E N A)))
    (hβ : ∀ i, IsIso (β i))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsIso (substituteInputs l E N M β good A) := by
  induction A with
  | input i => simpa only [substituteInputs, value, strictValue, expression,
      IntegralCoherence.value, Pi.eval_obj] using hβ i
  | unitY =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      infer_instance
  | unitX =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      infer_instance
  | unitZ =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      infer_instance
  | tensor A B hA hB =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      have := hB
      exact tensor_substitution_iso l E _ _ (good A) (good B) _ _ (hn A) (hn B)
  | pullF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      exact pull_substitution_iso l E f _ _ (hn A)
  | pullH A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      exact pull_substitution_iso l E h _ _ (hn A)
  | pullHF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value, substituteInputs]
      have := hA
      exact pull_substitution_iso l E (h ≫ f) _ _ (hn A)

private theorem constructible_complete {Y : Scheme.{u}}
    (M : sfIntegralConstructibleCategory l E Y) :
    IntegralOnSlice.IsComplete l E Y none M.obj := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1,
    cardinality_eq := by simp, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E Y D hl M.obj).mp M.property.1⟩

private theorem substitution_iso {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (hn : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A) := by
  unfold substitution
  apply substitute_inputs_iso l E _ _ _ good hn
  intro i
  have := (purNormalizedReconstructionOfScheme l E Y (pullbackTensorCalculus l E Y)).2
    (M i).obj (constructible_complete l E (M i))
  exact ((asIso ((pullbackTensorCalculus l E Y).adjunction.unit.app (M i).obj)) ≪≫
    (coefficientSequenceLimit l E Y).mapIso
      ((pullbackTensorCalculus l E Y).reduction.mapIso (φ i).symm ≪≫
        (pullbackTensorReductionModel l E Y).app (P i))).isIso_hom

private local instance (priority := 10000) sequenceMonoidal (W : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules l E W) :=
  SheafOfModules.monoidalCategory (coefficientSequenceCommRingSheaf l E W)

private local instance (priority := 10000) complexMonoidal (W : Scheme.{u}) :
    MonoidalCategory (StrictQuotient.Complex l E W) :=
  HomologicalComplex.monoidalCategory (coefficientSequenceModules l E W) (.up ℤ)

private theorem reduction_naturality {W : Scheme.{u}}
    {K K' : DerivedCategory (scalarReductionSource l E W)}
    {A A' : coefficientSequenceDerived l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj A)
    (β' : K' ⟶ (coefficientSequenceLimit l E W).obj A')
    (k : K ⟶ K') (a : A ⟶ A')
    (hc : k ≫ β' = β ≫ (coefficientSequenceLimit l E W).map a) :
    (pullbackTensorCalculus l E W).reduction.map k ≫ reduction l E β' =
      reduction l E β ≫ a := by
  unfold reduction
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
    congrArg ((pullbackTensorCalculus l E W).reduction.map β ≫ ·)
      ((pullbackTensorCalculus l E W).adjunction.counit.naturality a)

private theorem tensor_substitution_naturality {W : Scheme.{u}}
    {K K' H H' : DerivedCategory (scalarReductionSource l E W)}
    {A A' B B' : StrictQuotient.Complex l E W}
    (hA : StrictQuotient.SystemGood l E A) (hA' : StrictQuotient.SystemGood l E A')
    (hB : StrictQuotient.SystemGood l E B) (hB' : StrictQuotient.SystemGood l E B')
    (βA : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (βA' : K' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A'))
    (βB : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B))
    (βB' : H' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B'))
    (k : K ⟶ K') (j : H ⟶ H') (a : A ⟶ A') (b : B ⟶ B')
    (ha : k ≫ βA' = βA ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a))
    (hb : j ≫ βB' = βB ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map b)) :
    (integralCompletedTensor l E W).map (Prod.mkHom k j) ≫
        tensorSubstitution l E A' B' hA' hB' βA' βB' =
      tensorSubstitution l E A B hA hB βA βB ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map
          ((coefficientTotalTensor.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b))) := by
  let R := (pullbackTensorCalculus l E W).reduction
  let L := coefficientSequenceLimit l E W
  let T := (pullbackTensorCalculus l E W).systemClosed.tensor
  have hd : Prod.mkHom (R.map k) (R.map j) ≫
        Prod.mkHom (reduction l E βA') (reduction l E βB') =
      Prod.mkHom (reduction l E βA) (reduction l E βB) ≫
        Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) := by
    ext
    · exact reduction_naturality l E βA βA' k (DerivedCategory.Q.map a) ha
    · exact reduction_naturality l E βB βB' j (DerivedCategory.Q.map b) hb
  have ht : (integralCompletedTensor l E W).map (Prod.mkHom k j) ≫
      (pullbackTensorIntegralTensorModel l E W).hom.app (K', H') =
      (pullbackTensorIntegralTensorModel l E W).hom.app (K, H) ≫
        L.map (T.map (Prod.mkHom (R.map k) (R.map j))) :=
    (pullbackTensorIntegralTensorModel l E W).hom.naturality (Prod.mkHom k j)
  have hs : T.map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        (pullbackTensorSystemModel l E W A' B' hA'.1 hB'.1).inv =
      (pullbackTensorSystemModel l E W A B hA.1 hB.1).inv ≫
        DerivedCategory.Q.map ((coefficientTotalTensor.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)) := by
    exact (pullbackTensorCalculus l E W).systemTensorModel.comparison.inv.naturality
      (Prod.mkHom
        (show (⟨A, hA.1⟩ : ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E W))) ⟶
          ⟨A', hA'.1⟩ from ⟨a⟩)
        (show (⟨B, hB.1⟩ : ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E W))) ⟶
          ⟨B', hB'.1⟩ from ⟨b⟩))
  unfold tensorSubstitution
  change _ ≫ _ ≫ L.map (T.map _) ≫ L.map _ =
    (_ ≫ L.map (T.map _) ≫ L.map _) ≫ L.map _
  simp only [Category.assoc]
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc, ← T.map_comp, hd, T.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [← L.map_comp, hs, L.map_comp]

private theorem pull_substitution_naturality {V W : Scheme.{u}} (g : V ⟶ W)
    {K K' : DerivedCategory (scalarReductionSource l E W)}
    {A A' : StrictQuotient.Complex l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (β' : K' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A'))
    (k : K ⟶ K') (a : A ⟶ A')
    (hc : k ≫ β' = β ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a)) :
    (integralDerivedPullback l E g).map k ≫ pullSubstitution l E g A' β' =
      pullSubstitution l E g A β ≫ (coefficientSequenceLimit l E V).map
        (DerivedCategory.Q.map ((IntegralCoherence.pull l E g).map a)) := by
  let L := coefficientSequenceLimit l E V
  let F := pullbackTensorSequenceDerived l E g
  let e : DerivedCategory.Q ⋙ F ≅
      (IntegralCoherence.pull l E g) ⋙ DerivedCategory.Q :=
    (pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (pullBridge l E g) DerivedCategory.Q
  have he := e.hom.naturality a
  dsimp only [Functor.comp_map] at he
  have hd := reduction_naturality l E β β' k (DerivedCategory.Q.map a) hc
  have ht : (integralDerivedPullback l E g).map k ≫
      (pullbackTensorIntegralPullbackModel l E g).hom.app K' =
      (pullbackTensorIntegralPullbackModel l E g).hom.app K ≫
        L.map (F.map ((pullbackTensorCalculus l E W).reduction.map k)) :=
    (pullbackTensorIntegralPullbackModel l E g).hom.naturality k
  unfold pullSubstitution
  change _ ≫ _ ≫ L.map (F.map _) ≫ L.map (e.hom.app A') =
    (_ ≫ L.map (F.map _) ≫ L.map (e.hom.app A)) ≫ L.map _
  simp only [Category.assoc]
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc, ← F.map_comp, hd, F.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [← L.map_comp, he, L.map_comp]

private theorem substitute_inputs_naturality
    {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (N N' : Fin 3 → StrictQuotient.Complex l E Y)
    (M M' : Fin 3 → DerivedCategory (scalarReductionSource l E Y))
    (β : ∀ i : Fin 3, M i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N i)))
    (β' : ∀ i : Fin 3, M' i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N' i)))
    (good : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l E (strictValue l E N A))
    (good' : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l E (strictValue l E N' A))
    (a : ∀ i, N i ⟶ N' i) (v : ∀ i, M i ⟶ M' i)
    (hc : ∀ i, v i ≫ β' i = β i ≫
      (coefficientSequenceLimit l E Y).map (DerivedCategory.Q.map (a i)))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    (value l E A).map v ≫ substituteInputs l E N' M' β' good' A =
      substituteInputs l E N M β good A ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map (strictMap l E a A)) := by
  induction A with
  | input i => simpa only [value, strictValue, expression, IntegralCoherence.value,
      substituteInputs, strictMap, Pi.eval_map, Pi.eval_obj] using hc i
  | unitY =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (coefficientSequenceLimit l E Y).map
        (DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorUnit
          (coefficientSequenceModules l E Y) (.up ℤ))))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  | unitX =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorUnit
          (coefficientSequenceModules l E X) (.up ℤ))))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  | unitZ =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (coefficientSequenceLimit l E Z).map
        (DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorUnit
          (coefficientSequenceModules l E Z) (.up ℤ))))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  | tensor A B hA hB =>
      have ht := tensor_substitution_naturality l E (good A) (good' A) (good B) (good' B)
        _ _ _ _ _ _ _ _ hA hB
      rw [RingedDerivedNative.totalTensor_map_eq.{u+1, u, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology _))
        (coefficientSequenceCommRingSheaf l E _) _ _ _ _ _ _] at ht
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map, Functor.prod'_map,
        Functor.comp_obj, Functor.prod'_obj]
      dsimp only [StrictQuotient.total, coefficientTotalTensor,
        HomologicalComplex.monoidalCategory, CategoryTheory.Monoidal.induced,
        HomologicalComplex.monoidalCategoryStruct] at ht ⊢
      exact ht
  | pullF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map]
      exact pull_substitution_naturality l E f _ _ _ _ hA
  | pullH A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map]
      exact pull_substitution_naturality l E h _ _ _ _ hA
  | pullHF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map]
      exact pull_substitution_naturality l E (h ≫ f) _ _ _ _ hA

private theorem substitution_naturality {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P) : NaturalSubstitution l E M P φ good := by
  unfold NaturalSubstitution
  intro M' P' φ' good' a v comm W A
  unfold substitution
  apply substitute_inputs_naturality
  intro i
  let L := coefficientSequenceLimit l E Y
  let R := (pullbackTensorCalculus l E Y).reduction
  let e := pullbackTensorReductionModel l E Y
  have hφ : v i ≫ (φ' i).inv = (φ i).inv ≫ DerivedCategory.Q.map (a i) := by
    apply (cancel_mono (φ' i).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, comm i,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he : R.map (DerivedCategory.Q.map (a i)) ≫ e.hom.app (P' i) =
      e.hom.app (P i) ≫ DerivedCategory.Q.map
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).map
          (a i)) := by
    exact e.hom.naturality (show P i ⟶ P' i from ⟨a i⟩)
  change v i ≫ (pullbackTensorCalculus l E Y).adjunction.unit.app (M' i).obj ≫
      L.map (R.map (φ' i).inv ≫ e.hom.app (P' i)) =
    ((pullbackTensorCalculus l E Y).adjunction.unit.app (M i).obj ≫
      L.map (R.map (φ i).inv ≫ e.hom.app (P i))) ≫ L.map _
  rw [← Category.assoc, ← (pullbackTensorCalculus l E Y).adjunction.unit_naturality,
    Category.assoc, ← L.map_comp, ← R.map_comp_assoc, hφ, R.map_comp_assoc, he,
    ← Category.assoc, L.map_comp, Category.assoc]


set_option linter.unusedVariables false in
/-- Quotient normalization and recursive substitution.
Source: realization proof step 1 and representative naturality in step 3;
Stacks 07A2, 0G7E and 0941
(blueprint: lem-pur-completed-comparison-quotient-normalization).

Proof: use the ordinary quotient tower of each prescribed representative. The
ordinary evaluation adjunction identifies its levels and every quotient transition.
K-flatness and flat terms survive reduction; the normalized quotient adjoints are
the balanced maps. Induct on the expression: units are flat K-flat normalized,
tensor preserves these properties, and constant-coefficient inverse image does too.
At a leaf, derived completeness makes the actual reconstruction unit invertible.
Tensor and inverse-image steps use the primitive counit comparisons, with the
normalized effective counit, so both substitution and its coherent reduction are
invertible. The reduction model and evaluation adjunction give the stated
presentation. Naturality holds at leaves by the reconstruction unit and the
reduction-model naturality. Induction, primitive naturality and functoriality of
tensor and inverse image prove it at each remaining constructor. All calculations
are in the category of whole coefficient systems before evaluation. -/
theorem completedComparisonQuotientNormalization
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    :
    ∃ (good : GoodExpressions l E h f P)
      (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
        IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)),
    (∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      (∀ n : ℕ, StrictQuotient.Good l E
        (strictValue l E (fun i ↦ quotient l E (P i).obj) A) n) ∧
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) ∧
      IsIso (reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A))) ∧
    (∀ i : Fin 3, CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      (P i).obj (P i).property.1 (quotient l E (P i).obj)
      ((pullbackTensorReductionModel l E Y).app (P i))
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm)) ∧
    NaturalSubstitution l E M P φ good := by
  let good : GoodExpressions l E h f P := expressions_good l E h f P
  have hpres := fun i : Fin 3 ↦ completedQuotientReductionPresentation l E Y (P i)
  have hn : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) :=
    fun A ↦ expressions_normalized l E h f P hpres A
  have hb : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A) :=
    fun A ↦ substitution_iso l E M P φ good hn A
  refine ⟨good, hb, ?_, hpres, substitution_naturality l E M P φ good⟩
  intro W A
  have := hb A
  exact ⟨(StrictQuotient.levelwiseFlatModels l E W _).2 (good A),
    hn A, reduction_iso l E _ (hn A)⟩

end WeilConjectures.CompletedQuotient
