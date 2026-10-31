/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import all WeilConjectures.AlgebraicGeometry.CoefficientNormalizedInternalHomFibers
import WeilConjectures.AlgebraicGeometry.CoefficientNormalizedEvaluationProjection
import all WeilConjectures.CategoryTheory.CoefficientSequenceGlobalSections
import all WeilConjectures.SixFunctors.CoefHomScalarNaturality
import all WeilConjectures.AlgebraicGeometry.CoefSupportPointSectionsModelExistence
import all WeilConjectures.AlgebraicGeometry.CompactSupportFiniteAction
import WeilConjectures.SixFunctors.IntegralDualizingSystemFiniteProjection
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor

/-! # Assembly of finite trace tests

Source: prop-coef-integral-dualizing, proof paragraph 2, finite trace test.
(blueprint: lem-coef-system-finite-trace-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem representable_sections_map_injective
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (L : D ⥤ A) (R : A ⥤ D) (a : L ⊣ R)
    (J : C ⥤ D) (V : D ⥤ C) (b : J ⊣ V)
    (E : A ⥤ B) (H : B ⥤ C) (β : R ⋙ V ≅ E ⋙ H)
    (T : C) (N : A) :
    Function.Injective (fun f : L.obj (J.obj T) ⟶ N ↦ E.map f) := by
  intro f g h
  apply (a.homEquiv _ _).injective
  apply (b.homEquiv _ _).injective
  have hr : V.map (R.map f) = V.map (R.map g) := by
    apply (cancel_mono (β.hom.app N)).mp
    have h' : E.map f = E.map g := h
    calc
      V.map (R.map f) ≫ β.hom.app N =
          β.hom.app _ ≫ H.map (E.map f) := β.hom.naturality f
      _ = β.hom.app _ ≫ H.map (E.map g) := by rw [h']
      _ = V.map (R.map g) ≫ β.hom.app N := (β.hom.naturality g).symm
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [hr]

private theorem closed_transpose_evaluation_injective
    {A B : Type*} [Category A] [Category B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure HA) (R : CoefficientClosedStructure HB)
    (E : A ⥤ B) (μ : S.tensor ⋙ E ≅ E.prod E ⋙ R.tensor)
    (M N : A) (γ : E.obj (HA.obj (op M, N)) ≅
      HB.obj (op (E.obj M), E.obj N))
    (hγ : R.tensor.map (Prod.mkHom γ.hom (𝟙 (E.obj M))) ≫
      R.evaluation (E.obj M) (E.obj N) =
      μ.inv.app (HA.obj (op M, N), M) ≫ E.map (S.evaluation M N))
    (Z : A) (f g : S.tensor.obj (Z, M) ⟶ N) (h : E.map f = E.map g) :
    E.map (S.transpose Z M N f) = E.map (S.transpose Z M N g) := by
  have he (q : Z ⟶ HA.obj (op M, N)) :
      (R.transpose (E.obj Z) (E.obj M) (E.obj N)).symm (E.map q ≫ γ.hom) =
        μ.inv.app (Z, M) ≫ E.map ((S.transpose Z M N).symm q) := by
    rw [uncurry_formula, uncurry_formula]
    have ht : Prod.mkHom (E.map q ≫ γ.hom) (𝟙 (E.obj M)) =
        Prod.mkHom (E.map q) (𝟙 (E.obj M)) ≫
          Prod.mkHom γ.hom (𝟙 (E.obj M)) := by simp
    rw [ht, Functor.map_comp, Category.assoc, hγ, ← Category.assoc]
    have hn := μ.inv.naturality (Prod.mkHom q (𝟙 M))
    simpa only [Functor.comp_map, Functor.prod_map, E.map_id, Functor.map_comp,
      Category.assoc] using congrArg (fun z ↦ z ≫ E.map (S.evaluation M N)) hn
  apply (cancel_mono γ.hom).mp
  apply (R.transpose (E.obj Z) (E.obj M) (E.obj N)).symm.injective
  rw [he, he]
  simp only [Equiv.symm_apply_apply, h]

private theorem pairingSections_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u}) (n : ℕ) :
    Nonempty (coefPairingSections l E W ⋙ coefPairingDerivedEvaluation l E n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        coefficientFiniteDerivedRestriction l E W n ⋙
          CoefSupportOpenTensor.levelSections l E W) := by
  let f := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E W)
  let g := coefTraceSections l E W
  let r := coefficientSequenceRestriction l E W
  let c : coefPairingSections l E W ≅
      coefficientSequenceDerivedRestriction l E W ⋙
        CoefSupportOpenTensor.integralSections l E W :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso r f) g.rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft r.mapDerivedCategory
        (derivedComposite f g (fun I hI ↦ by
          have := hI
          exact coefCompletedTowerSections_acyclic l E W I)).symm
  let F := CoefSupportOpenTensor.ordinaryLevelSections l E W
  let P := CoefSupportOpenTensor.actualSectionsDerivedPair F
  let T := CoefSupportOpenTensor.actualSectionsDerivedPair
    (CoefSupportOpenTensor.ordinarySections l E W)
  obtain ⟨β, _, _⟩ := SheafOfModules.coefficientTowerComparison F P T (fun K ↦ by
    obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, ha⟩)
  exact ⟨Functor.isoWhiskerRight c (coefPairingDerivedEvaluation l E n) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E W) (β (op n)) ≪≫
    Functor.isoWhiskerRight (coefficientRestrictedEvaluationIso l E W n)
      (CoefSupportOpenTensor.levelSections l E W)⟩

private theorem normalized_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    {M N : coefficientSequenceDerived l E W} (e : M ≅ N)
    (hM : IsNormalizedCoefficientSequence l E W M) :
    IsNormalizedCoefficientSequence l E W N := by
  intro m n h P
  let Em := coefficientSequenceDerivedEvaluation l E W m
  let En := coefficientSequenceDerivedEvaluation l E W n
  let R := normalizedDVRRes l E W h
  let τ := coefficientSequenceDerivedTransition l E W h
  constructor
  · intro f g hf
    change τ.app N ≫ R.map f = τ.app N ≫ R.map g at hf
    have hn := τ.naturality e.hom
    change Em.map e.hom ≫ τ.app N = τ.app M ≫ R.map (En.map e.hom) at hn
    have heq : En.map e.hom ≫ f = En.map e.hom ≫ g := by
      apply (hM h P).injective
      change τ.app M ≫ R.map (En.map e.hom ≫ f) =
        τ.app M ≫ R.map (En.map e.hom ≫ g)
      simp only [Functor.map_comp, ← Category.assoc]
      simpa only [← hn, Category.assoc] using
        congrArg (fun q ↦ Em.map e.hom ≫ q) hf
    exact (cancel_epi (En.map e.hom)).mp heq
  · intro f
    obtain ⟨g, hg⟩ := (hM h P).surjective (Em.map e.hom ≫ f)
    change τ.app M ≫ R.map g = Em.map e.hom ≫ f at hg
    refine ⟨En.map e.inv ≫ g, ?_⟩
    have hn := τ.naturality e.inv
    change Em.map e.inv ≫ τ.app M = τ.app N ≫ R.map (En.map e.inv) at hn
    change τ.app N ≫ R.map (En.map e.inv ≫ g) = f
    rw [Functor.map_comp, ← Category.assoc, ← hn]
    rw [Category.assoc, hg]
    simp only [← Category.assoc, ← Em.map_comp, Iso.inv_hom_id, Em.map_id]
    exact Category.id_comp f

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- Assemble a system Hom bijection from the finite evaluation bijection for the
same representable test. This is the tower-level assembly step and contains no
finite duality or site-comparison argument.

Source: prop-coef-integral-dualizing, proof paragraph 2 (finite trace test);
Stacks 0941.
(blueprint: lem-coef-system-finite-trace-assembly).

Proof: write F for the displayed system map g ↦ support(g) ≫ t.trace and ev for
the map h ↦ (evaluation at n of h) ≫ (t.unitEvaluation n).hom on maps from the
compact support of the test V to the base unit. The map in hfin is ev ∘ F, so F
is injective, and F is surjective once ev is injective. The representable tower
(coefPairingEvaluationLeft n) is the given test at levels m ≤ n with identity
transitions and zero above n. The proper projection theorem and inverse open
tensor comparison identify compact support of V with sstar of that test tensor
M, where M is compact support of the reduction of K. The integral residue-Tor
criterion and compact-support normalization, transported by t.supportComparison,
make M normalized. Normalized evaluation projection and its closed mate identify
evaluated internal Hom from M with finite internal Hom from its evaluation.
The evaluation equation for this comparison implies that equal evaluated maps
have equal evaluated closed transposes. Derived sections commute with evaluation:
factor the scalar restriction composite, use the K-injective tower comparison,
and then the restricted-evaluation isomorphism. Naturality of this sections
comparison and the two adjunctions (sstar/sections and tower induction/evaluation)
show that evaluation detects maps from sstar of the representable test. Cancel
the closed transpose and projection isomorphisms to obtain injectivity of ev.
Consequently F is bijective. -/
theorem integralDualizingSystem_finite_trace_assembly
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (t : IntegralDualizingSystemTraceData D l E X S G Q eQ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
    (hfin : Function.Bijective (fun g :
      S.systemClosed.tensor.obj
        ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
          ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K) ⟶ coefTraceInput l E X Q ↦
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
        (G.properModules.rightDerivedFunctor.map (G.openModules.mapDerivedCategory.map g)) ≫
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map t.trace ≫
        (t.unitEvaluation n).hom)) :
    Function.Bijective (fun g :
      S.systemClosed.tensor.obj
        ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
          ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K) ⟶ coefTraceInput l E X Q ↦
      G.properModules.rightDerivedFunctor.map (G.openModules.mapDerivedCategory.map g) ≫
        t.trace) := by
  classical
  let Y := Spec (.of D.k)
  let c := finiteDualizingCompactification D X
  let J := G.openModules.mapDerivedCategory
  let P := G.properModules.rightDerivedFunctor
  let V := coefficientSequenceDerivedEvaluation l E Y n
  let H := (coefPairingEvaluationLeft l E n).obj T
  let Z := G.frame.sstar.obj H
  let M := P.obj (J.obj (S.reduction.obj K))
  let U := G.baseTensors.systemClosed.monoidal.tensorUnit
  let W := S.systemClosed.tensor.obj
    ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj H, S.reduction.obj K)
  let F : (W ⟶ coefTraceInput l E X Q) → (P.obj (J.obj W) ⟶ U) :=
    fun g ↦ P.map (J.map g) ≫ t.trace
  let ev : (P.obj (J.obj W) ⟶ U) → (V.obj (P.obj (J.obj W)) ⟶ V.obj U) :=
    fun h ↦ V.map h
  have hb : Function.Bijective (ev ∘ F) := by
    constructor
    · intro f g h
      apply hfin.1
      change V.map (P.map (J.map f)) ≫ V.map t.trace ≫ (t.unitEvaluation n).hom =
        V.map (P.map (J.map g)) ≫ V.map t.trace ≫ (t.unitEvaluation n).hom
      simpa only [ev, F, Function.comp_apply, Functor.map_comp, Category.assoc] using
        congrArg (fun k ↦ k ≫ (t.unitEvaluation n).hom) h
    · intro h
      obtain ⟨g, hg⟩ := hfin.2 (h ≫ (t.unitEvaluation n).hom)
      refine ⟨g, ?_⟩
      apply (cancel_mono (t.unitEvaluation n).hom).mp
      simpa only [ev, F, Function.comp_apply, Functor.map_comp, Category.assoc] using hg
  have hpoint : Function.Injective ev := by
    have hp := integralDualizingSystem_finite_test_projection_isIso
      D l hl E X S G K hK n T
    let p := G.frame.testProjection S.systemClosed G.baseTensors.systemClosed H
      (S.reduction.obj K)
    have : IsIso p := by
      dsimp only [p, CategoryTheory.CoefPairingFrame.testProjection]
      infer_instance
    let (x : X) : Invertible (l : X.residueField x) :=
      (show IsUnit (l : X.residueField x) by
        simpa using (finiteFieldDatumPrimeUnit D l hl).map
          ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
    have hKi : sfIntegralConstructible l E X K := by
      rw [(integral_residue_tor D l hl E X).2]
      exact hK
    let : Y.Over Y := ⟨𝟙 _⟩
    let : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
    have hMN : IsNormalizedCoefficientSequence l E Y
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i ⋙
          ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K)) :=
      compactSupportSystem_normalized l c D.k (finiteFieldDatumPrimeUnit D l hl)
        E ⟨K, hKi⟩ S
    have hM : IsNormalizedCoefficientSequence l E Y M :=
      normalized_of_iso l E Y (t.supportComparison.app (S.reduction.obj K)).symm hMN
    obtain ⟨R, hRT, _, _, hE, _, _⟩ :=
      coefficientNormalizedReductionModels l E Y G.baseTensors
    have := coefficientEvaluation_rightAdjoint l E Y n
    let L := V.leftAdjoint
    let adj := Adjunction.ofIsRightAdjoint V
    obtain ⟨γ, hγ⟩ := closed_evaluation_of_projection R.systemClosed (R.finiteClosed n)
      V L adj (R.evaluationTensor n) M
      (coefficientNormalizedEvaluationProjection l E Y R hE M hM n L adj)
    let e := ((R.systemClosed.adjunction M).leftAdjointUniq
      (G.baseTensors.systemClosed.adjunction M)).app Z
    obtain ⟨β⟩ := pairingSections_evaluation l E Y n
    intro f g h
    have hc : V.map (R.systemClosed.transpose Z M U (e.hom ≫ p ≫ f)) =
        V.map (R.systemClosed.transpose Z M U (e.hom ≫ p ≫ g)) :=
      closed_transpose_evaluation_injective R.systemClosed (R.finiteClosed n)
        V (R.evaluationTensor n) M U (γ.app U) (hγ U) Z _ _ (by
          change V.map f = V.map g at h
          simp only [Functor.map_comp, h])
    have ht : R.systemClosed.transpose Z M U (e.hom ≫ p ≫ f) =
        R.systemClosed.transpose Z M U (e.hom ≫ p ≫ g) :=
      representable_sections_map_injective G.frame.sstar (coefPairingSections l E Y)
        G.frame.sectionsAdjunction (coefPairingEvaluationLeft l E n)
        (coefPairingDerivedEvaluation l E n) (coefPairingEvaluationAdjunction l E n)
        V (coefficientFiniteDerivedRestriction l E Y n ⋙
          CoefSupportOpenTensor.levelSections l E Y) β T _ hc
    have hu := (R.systemClosed.transpose Z M U).injective ht
    exact (cancel_epi p).mp ((cancel_epi e.hom).mp hu)
  exact Function.Bijective.of_comp_left hb hpoint

end WeilConjectures
