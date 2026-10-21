/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CoefficientExtensionReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import Sheaf.Paper.CoefficientSequenceRoosModel
import Sheaf.Paper.NormalizedDVRRoosFiniteReduction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic
import Sheaf.Paper.CoefficientExtensionFiniteAssociation
import Sheaf.Paper.CoefficientExtensionStrictRepresentatives
import Sheaf.Paper.CoefficientExtensionRepresentativeRoos
/-! # Coherent finite reduction of completed coefficient extension

Source: main-20261015 blueprint, sec-proetale-coefficients/sk-def-sf-operations,
def-weil-derived-pullback-tensor-hom, integral operations; Stacks 06YS, 0G7E, 06YY.
(blueprint: lem-pur-coefficient-extension-reduction-model).
Positive exponent m is encoded by n=m-1. All derived categories are unbounded,
and the small pro-etale site's object and morphism universes remain independent.

## Main definitions

- `CoefficientExtensionReductionData`: simultaneous models and their canonical counit.
- `coefficientExtensionReductionIso`: that counit as a coherent-system isomorphism.

## Main statements

- `coefficientExtensionReductionModel`: existence on the entire unbounded derived category.
- `coefficientExtensionReduction_identity`: normalization for identity coefficients.
- `coefficientExtensionReduction_composition`: compatibility for three coefficient fields.
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
section ScalarAssociation
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  {R S T : Sheaf J CommRingCat.{max c v r}} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T}
  (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
  (B : SemilinearSections.ScalarData.{c, v, max c v r} g)
  (D : SemilinearSections.ScalarData.{c, v, max c v r} h)

private theorem scalarSection_eq_unit {f : R ⟶ S}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
    (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x =
      @id ((A.model.E.obj M).val.obj U)
        ((A.ordinaryAdjunction.unit.app M).val.app U x) := by
  unfold SemilinearSections.scalarExtensionSection
  rw [← A.unit_section M U x]
  erw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl]
  rfl

private theorem scalarTranspose_all {f : R ⟶ S}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J S) ℤ)
    (z : (A.model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q) :
    (A.adjunction.homEquiv _ _) (A.model.ε.app P ≫ DerivedCategory.Q.map z) ≫
        (SemilinearSections.res f).mapDerivedCategoryFactors.hom.app Q =
      DerivedCategory.Q.map
        (((A.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) z) := by
  obtain ⟨P', q, hP', _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  have : QuasiIso q := hq
  apply (cancel_epi (DerivedCategory.Q.map q)).1
  calc
    _ = (A.adjunction.homEquiv _ _)
          (A.model.ε.app P' ≫ DerivedCategory.Q.map
            ((A.model.E.mapHomologicalComplex (.up ℤ)).map q ≫ z)) ≫
          (SemilinearSections.res f).mapDerivedCategoryFactors.hom.app Q := by
      rw [← Category.assoc, ← Adjunction.homEquiv_naturality_left]
      congr 1
      rw [Functor.map_comp, ← Category.assoc]
      congr 1
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ k ≫ DerivedCategory.Q.map z) (A.model.ε.naturality q)
    _ = _ := A.transpose_model P' Q hP' _
    _ = _ := by
      rw [Adjunction.homEquiv_naturality_left, Functor.map_comp]

private def scalarRestrictionCompIso (hf : f ≫ g = h) :
    SemilinearSections.res.{c, v, max c v r} g ⋙
      SemilinearSections.res.{c, v, max c v r} f ≅
      SemilinearSections.res.{c, v, max c v r} h :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
          (h.hom.app U).hom (congrArg (fun z ↦ (z.hom.app U).hom) hf.symm)
          (M.val.obj U)).symm) (by intros; ext x; rfl))) (by intros; ext U x; rfl)

private theorem scalarAssociation_ordinary_formula (hf : f ≫ g = h) :
    let adj := (A.ordinaryAdjunction.comp B.ordinaryAdjunction).ofNatIsoRight
      (scalarRestrictionCompIso.{c, v, r} hf)
    let a := adj.leftAdjointUniq D.ordinaryAdjunction
    ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
      (s : S.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U),
        (a.hom.app M).val.app U
          (t • SemilinearSections.scalarExtensionSection.{c, v, r} g B (A.model.E.obj M) U
            (s • SemilinearSections.scalarExtensionSection.{c, v, r} f A M U x)) =
          (((g.hom.app U) s * t) •
            SemilinearSections.scalarExtensionSection.{c, v, r} h D M U x) := by
  let adj := (A.ordinaryAdjunction.comp B.ordinaryAdjunction).ofNatIsoRight
    (scalarRestrictionCompIso.{c, v, r} hf)
  let a := adj.leftAdjointUniq D.ordinaryAdjunction
  dsimp only
  intro M U s t x
  rw [scalarSection_eq_unit, scalarSection_eq_unit, scalarSection_eq_unit]
  have hu := adj.unit_leftAdjointUniq_hom_app D.ordinaryAdjunction M
  have hx := congrArg (fun z ↦ (z.val.app U) x) hu
  dsimp only [adj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app] at hx
  change (a.hom.app M).val.app U
      ((B.ordinaryAdjunction.unit.app (A.model.E.obj M)).val.app U
        ((A.ordinaryAdjunction.unit.app M).val.app U x)) =
    (D.ordinaryAdjunction.unit.app M).val.app U x at hx
  rw [map_smul]
  have hs := ((B.ordinaryAdjunction.unit.app (A.model.E.obj M)).val.app U).hom.map_smul s
    ((A.ordinaryAdjunction.unit.app M).val.app U x)
  change (B.ordinaryAdjunction.unit.app (A.model.E.obj M)).val.app U
      (s • @id ((A.model.E.obj M).val.obj U)
        ((A.ordinaryAdjunction.unit.app M).val.app U x)) =
    (g.hom.app U s) • @id ((B.model.E.obj (A.model.E.obj M)).val.obj U)
      ((B.ordinaryAdjunction.unit.app (A.model.E.obj M)).val.app U
        ((A.ordinaryAdjunction.unit.app M).val.app U x)) at hs
  rw [hs]
  dsimp only [id]
  erw [map_smul, hx, smul_smul, mul_comm]

private theorem scalarTranspose_comp (hf : f ≫ g = h)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J T) ℤ)
    (z : (B.model.E.mapHomologicalComplex (.up ℤ)).obj
      ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ⟶ Q) :
    let ρ := scalarRestrictionCompIso.{c, v, r} hf
    let ρD := Functor.mapDerivedCategoryCompNatIso ρ
    let adj := (A.adjunction.comp B.adjunction).ofNatIsoRight ρD
    adj.homEquiv _ _
        (B.T.map (A.model.ε.app P) ≫
          B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map z) ≫
        (SemilinearSections.res h).mapDerivedCategoryFactors.hom.app Q =
      DerivedCategory.Q.map
        ((((A.ordinaryAdjunction.comp B.ordinaryAdjunction).ofNatIsoRight ρ).mapHomologicalComplex
          (.up ℤ)).homEquiv P Q z) := by
  dsimp only
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Category.assoc,
    Functor.mapDerivedCategoryCompNatIso_hom_app_Q]
  rw [Adjunction.comp_homEquiv]
  change (A.adjunction.homEquiv _ _) ((B.adjunction.homEquiv _ _) _) ≫ _ = _
  erw [← Category.assoc, ← Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left]
  simp only [Category.assoc]
  erw [scalarTranspose_all.{c, v, r} B
    ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) Q z]
  change (A.adjunction.homEquiv _ _)
      (A.model.ε.app P ≫ DerivedCategory.Q.map
        ((B.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _ z)) ≫ _ = _
  erw [← Category.assoc, scalarTranspose_all.{c, v, r} A P
    (((SemilinearSections.res g).mapHomologicalComplex (.up ℤ)).obj Q)
    ((B.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _ z),
    ← DerivedCategory.Q.map_comp]
  congr 1

private theorem scalarAssociation_exists (hf : f ≫ g = h) :
    Nonempty (CoefficientScalarAssociation.{c, v, r} A B D) := by
  let ρ := scalarRestrictionCompIso.{c, v, r} hf
  let adjO := (A.ordinaryAdjunction.comp B.ordinaryAdjunction).ofNatIsoRight ρ
  let a := adjO.leftAdjointUniq D.ordinaryAdjunction
  let adjD := (A.adjunction.comp B.adjunction).ofNatIsoRight
    (Functor.mapDerivedCategoryCompNatIso ρ)
  let d := adjD.leftAdjointUniq D.adjunction
  refine ⟨⟨a, scalarAssociation_ordinary_formula.{c, v, r} A B D hf, d, ?_⟩⟩
  intro P _
  apply (adjD.homEquiv _ _).injective
  apply (cancel_mono ((SemilinearSections.res h).mapDerivedCategoryFactors.hom.app
    ((D.model.E.mapHomologicalComplex (.up ℤ)).obj P))).1
  calc
    _ = (D.adjunction.homEquiv _ _) (D.model.ε.app P) ≫
        (SemilinearSections.res h).mapDerivedCategoryFactors.hom.app
          ((D.model.E.mapHomologicalComplex (.up ℤ)).obj P) := by
      rw [Adjunction.homEquiv_naturality_right,
        Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
    _ = DerivedCategory.Q.map
        ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hz := scalarTranspose_all.{c, v, r} D P
        ((D.model.E.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
      rw [DerivedCategory.Q.map_id] at hz
      erw [Category.comp_id, Adjunction.homEquiv_id] at hz
      exact hz
    _ = DerivedCategory.Q.map
        ((adjO.mapHomologicalComplex (.up ℤ)).homEquiv _ _
          ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P)) := by
      congr 1
      ext i : 1
      change D.ordinaryAdjunction.unit.app (P.X i) =
        adjO.homEquiv _ _ (a.hom.app (P.X i))
      exact (adjO.homEquiv_leftAdjointUniq_hom_app D.ordinaryAdjunction (P.X i)).symm
    _ = _ := (scalarTranspose_comp.{c, v, r} A B hf P _
      ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P)).symm

/-- Identity scalar extension is the adjoint unitor, including its universal derived model.
Source: the identity clause of integral operations and uniqueness of left derived functors
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
private theorem scalarUnit_exists {f : R ⟶ R}
    (A : SemilinearSections.ScalarData.{c, v, max c v r} f) (hf : f = 𝟙 R) :
    Nonempty (CoefficientScalarUnit.{c, v, r} A) := by
  subst f
  let ρ : SemilinearSections.res (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  let adj := A.ordinaryAdjunction.ofNatIsoRight ρ
  let a := adj.leftAdjointUniq Adjunction.id
  let Q := DerivedCategory.Q (C := SemilinearSections.Mod.{c, v, max c v r} J R)
  let b : A.model.E.mapHomologicalComplex (.up ℤ) ⋙ Q ≅ Q :=
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex a (.up ℤ)) Q ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ (.up ℤ)) Q ≪≫
      Functor.leftUnitor Q
  let W := HomologicalComplex.quasiIso
    (SemilinearSections.Mod.{c, v, max c v r} J R) (.up ℤ)
  have : A.T.IsLeftDerivedFunctor A.model.ε W := A.model.universal
  have : (𝟭 _).IsLeftDerivedFunctor (Functor.rightUnitor Q).hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ (Functor.rightUnitor Q)
  let d := Functor.leftDerivedNatIso A.T (𝟭 _) A.model.ε
    (Functor.rightUnitor Q).hom W b
  refine ⟨{ ordinary := a, derived := d, section_formula := ?_, model := ?_ }⟩
  · intro M U z x
    have hx : SemilinearSections.scalarExtensionSection.{c, v, r} (𝟙 R) A M U x =
        (A.ordinaryAdjunction.unit.app M).val.app U x := by
      unfold SemilinearSections.scalarExtensionSection
      rw [← A.unit_section M U x]
      erw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
        ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl]
      rfl
    rw [hx, (a.hom.app M).val.app U |>.hom.map_smul]
    congr 1
    have h := adj.unit_leftAdjointUniq_hom_app Adjunction.id M
    have h' := congrArg (fun z ↦ (z.val.app U) x) h
    exact h'
  · intro P hP
    have h := Functor.leftDerivedNatTrans_app A.T (𝟭 _) A.model.ε
      (Functor.rightUnitor Q).hom W b.hom P
    have hid : (Functor.mapHomologicalComplexIdIso
        (SemilinearSections.Mod.{c, v, max c v r} J R) (.up ℤ)).hom.app P = 𝟙 P := by
      ext i
      rfl
    change d.hom.app (Q.obj P) = A.model.ε.app P ≫ Q.map _
    change d.hom.app (Q.obj P) ≫ 𝟙 _ = A.model.ε.app P ≫ b.hom.app P at h
    dsimp only [b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
    erw [hid, Q.map_id, Category.comp_id, Category.comp_id] at h
    exact h

end ScalarAssociation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (SE : CoefficientDerivedSystemCalculus l E W)
  (SL : CoefficientDerivedSystemCalculus l L W)
  (A : CoefficientExtensionSystems l E L ι W)


/-- Construction of the normalized reduction skeleton from flat-term
representatives and finite quotient scalar association.
Source: integral operations and K-flat change of rings
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: choose a flat-term K-flat representative, form the finite quotient scalar
models, transport their balanced maps through every quotient transition, and
assemble the strict model, normalized tower, completion projection, and all
evaluation equations into the displayed skeleton. -/
theorem coefficientExtensionReductionSkeleton_exists
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    Nonempty (CoefficientExtensionReductionSkeleton l E L ι W SE A) := by
  classical
  obtain ⟨s⟩ := coefficientExtensionFiniteAssociation_exists l E L ι W A
  obtain ⟨direct, evaluation, model, ht, hm, hn⟩ :=
    coefficientExtensionStrictRepresentative_exists l E L ι W A SE
      s.association s.association_section
  obtain ⟨e, he⟩ := coefficientExtensionRepresentativeRoos_exists l E L ι W A SE
    direct evaluation ht model
  obtain ⟨α, hα, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι W).2.choose_spec.choose_spec.2.2.1
      (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W) e
  refine ⟨{
    association := s.association
    association_section := s.association_section
    direct := direct
    directEvaluation := evaluation
    direct_transition := ht
    model := model
    model_evaluation := hm
    normalized := hn
    completion := α.symm
    completion_projection := ?_
    comparison_isIso := trivial }⟩
  unfold IsCoefficientExtensionCompletionProjection
  intro P n
  have ha := congrArg (fun z ↦ z.hom.app P) hα
  change α.hom.app (DerivedCategory.Q.obj P.obj) ≫ e.hom.app P =
    (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P at ha
  have ha' : α.hom.app (DerivedCategory.Q.obj P.obj) =
      (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫
        e.inv.app P := by
    rw [← ha]
    erw [Category.assoc, e.hom_inv_id_app, Category.comp_id]
  change α.hom.app (DerivedCategory.Q.obj P.obj) ≫ _ ≫ _ ≫ _ = _
  rw [ha']
  simpa only [Category.assoc] using
    congrArg (fun f ↦ (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P ≫ f)
      (he P n)

private def effectivityTestDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private theorem normalizedSequence_counit_isIso
    (N : coefficientSequenceDerived l L W)
    (hN : IsNormalizedCoefficientSequence l L W N) :
    IsIso (SL.adjunction.counit.app N) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let D := effectivityTestDatum p hp
  have hlp : l ≠ D.p := by
    change l ≠ p
    omega
  obtain ⟨T, e, hprod, δ, hδ⟩ := coefficientSequence_roosModel l L W D hlp N hN
  let := hprod
  apply (SL.isIso_iff_evaluations _).2
  intro n
  let adj := coefficientFiniteAdjunction l L W n
  let q := (adj.homEquiv _ _).symm ((coefficientSequenceProjection l L W n).app N)
  have hi := normalizedDVRRoos_finite_reduction l L W D hlp T _ _ δ hδ n adj
  have heq : (adj.homEquiv _ _).symm
      ((Pi.lift (fun k : ℕ ↦ (coefficientSequenceProjection l L W k).app N ≫
        (normalizedDVRResCompleted l L W D hlp k).map (e k).inv ≫
        (T.evaluationIso k).inv)) ≫ Pi.π _ n ≫ (T.evaluationIso n).hom) =
      q ≫ (e n).inv := by
    simp only [Pi.lift_π_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact adj.homEquiv_naturality_right_symm _ _
  have : IsIso (q ≫ (e n).inv) := by
    rw [← heq]
    exact hi
  have : IsIso q := IsIso.of_isIso_comp_right q (e n).inv
  have hq : (SL.reductionEvaluation n).inv.app ((coefficientSequenceLimit l L W).obj N) ≫
      (coefficientSequenceDerivedEvaluation l L W n).map (SL.adjunction.counit.app N) = q := by
    apply (adj.homEquiv _ _).injective
    exact (SL.counit_projection N n).trans
      ((adj.homEquiv _ _).apply_symm_apply _).symm
  have : IsIso ((SL.reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l L W).obj N) ≫
      (coefficientSequenceDerivedEvaluation l L W n).map (SL.adjunction.counit.app N)) := by
    rw [hq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((SL.reductionEvaluation n).inv.app ((coefficientSequenceLimit l L W).obj N)) _

/-- The normalized tower counit of a reduction skeleton is invertible.
Source: normalized DVR effectivity
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: regard the skeleton's normalized sequence and completion projection as
the normalized DVR tower data, apply normalized effectivity to its Roos limit,
and identify the resulting canonical counit with `coefficientExtensionCounit`.
-/
theorem coefficientExtensionReductionSkeleton_comparison_isIso
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (s : CoefficientExtensionReductionSkeleton l E L ι W SE A) :
    IsIso (coefficientExtensionCounit l E L ι W SE SL A s.completion) := by
  have (K : DerivedCategory (scalarReductionSource l E W)) :
      IsIso (SL.adjunction.counit.app ((coefficientExtensionSystem l E L ι W SE A).obj K)) :=
    normalizedSequence_counit_isIso l L W SL _ (s.normalized K)
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro K
  unfold coefficientExtensionCounit
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- Coherent finite reduction of completed scalar extension on the entire derived category.
Source: integral operations, Stacks 06YS, 0G7E, 06YY
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: choose one flat-term K-flat P. Change of rings preserves K-flatness and flat
terms even for ramified quotient maps. The balanced maps (x⊗a)⊗b ↦ x⊗ι(a)b and
x⊗b ↦ (x⊗1)⊗b are inverse and commute with differentials. Quotient reduction
commutes with these formulas, giving a strict system isomorphism and normalization
by the same association with B_m→B_n. Its cocycle is the quotient cocycle. The
Roos construction computes the specified total limit and its projections, hence
completion. Apply normalized DVR effectivity with coefficient field L: its counit
is invertible and normalized by the actual limit projections. Transport it through
the simultaneous association to obtain exactly coefficientExtensionCounit.
Naturality on chain maps descends through the localization of flat-term K-flat
complexes; quasi-isomorphisms and roofs give the canonical resolution comparisons,
including their composition for a third representative. The equations hold for all
m≥n, including identities, because the comparison is a map of coherent systems.
For identity extension scalar association is the action unitor, so this is the
usual reduction counit of the completion, without assuming K itself complete.
For three fields the two scalar associations multiply the same coefficients.
Apply coefficient extension to this coherent counit and then use counit naturality
h e_H = e_J R_F L_F(h). This is an equality of system maps before evaluation,
and gives the composition equation stated below. No finiteness of K is used. -/
theorem coefficientExtensionReductionModel
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    Nonempty (CoefficientExtensionReductionData l E L ι W SE SL A) := by
  obtain ⟨s⟩ := coefficientExtensionReductionSkeleton_exists
    l E L ι W SE A _hl
  have hcomp := coefficientExtensionReductionSkeleton_comparison_isIso
    l E L ι W SE SL A _hl s
  refine ⟨⟨⟨⟨s.association, s.association_section⟩, s.direct,
    s.directEvaluation, s.direct_transition⟩, s.model, s.model_evaluation,
    s.normalized, s.completion, s.completion_projection, hcomp⟩⟩

section SuccessiveExtension
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F) (SF : CoefficientDerivedSystemCalculus l F W)
  (B : CoefficientExtensionSystems l L F j W)
  (D : CoefficientExtensionSystems l E F (j.comp ι) W)
  (dEL : CoefficientExtensionReductionData l E L ι W SE SL A)
  (dLF : CoefficientExtensionReductionData l L F j W SL SF B)
  (dEF : CoefficientExtensionReductionData l E F (j.comp ι) W SE SF D)

/-- Successive finite extension: extend the coherent E,L counit, then associate scalars.
Source: integral operations, node proof step 7
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionSuccessiveSystemIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        coefficientExtensionSystem l L F j W SL B ≅
      coefficientExtensionSystem l E F (j.comp ι) W SE D :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientExtensionReductionIso l E L ι W SE SL A dEL)
      B.scalar.T ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft SE.reduction a.derived

/-- The completed successive-extension comparison is the total limit of the same
coherent finite-system comparison.
Source: integral operations, node proof step 8
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
@[irreducible] def coefficientExtensionSuccessiveIso
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    integralScalarExtensionOfUniverses l E L ι W ⋙
        integralScalarExtensionOfUniverses l L F j W ≅
      integralScalarExtensionOfUniverses l E F (j.comp ι) W :=
  Functor.isoWhiskerLeft (integralScalarExtensionOfUniverses l E L ι W)
      dLF.completion.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a)
      (coefficientSequenceLimit l F W) ≪≫ dEF.completion

private theorem quotientSheaf_comp (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι W n ≫
        integralScalarQuotientSheafMap l L F j W n =
      integralScalarQuotientSheafMap l E F (j.comp ι) W n := by
  have hq : (integralScalarQuotientMap l L F j n).comp
      (integralScalarQuotientMap l E L ι n) =
      integralScalarQuotientMap l E F (j.comp ι) n := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  unfold integralScalarQuotientSheafMap
  rw [← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg ULift.up (RingHom.congr_fun hq x.down)

private theorem systemMap_comp :
    SemilinearSections.systemMap.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (coefficientExtensionQuotient_naturality l E L ι W) ≫
      SemilinearSections.systemMap.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralCoefficientCommRingSheaf l F W) (coefficientSequenceCommRingTransition l F W)
        (integralScalarQuotientSheafMap l L F j W)
        (coefficientExtensionQuotient_naturality l L F j W) =
      SemilinearSections.systemMap.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l F W) (coefficientSequenceCommRingTransition l F W)
        (integralScalarQuotientSheafMap l E F (j.comp ι) W)
        (coefficientExtensionQuotient_naturality l E F (j.comp ι) W) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rcases U with ⟨⟨n, U⟩⟩
  have hEL := (SemilinearSections.systemMap_existsUnique.{t + 1, t, max u (t + 1)}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (coefficientExtensionQuotient_naturality l E L ι W)).exists.choose_spec n (op U)
  have hLF := (SemilinearSections.systemMap_existsUnique.{t + 1, t, max u (t + 1)}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralCoefficientCommRingSheaf l F W) (coefficientSequenceCommRingTransition l F W)
    (integralScalarQuotientSheafMap l L F j W)
    (coefficientExtensionQuotient_naturality l L F j W)).exists.choose_spec n (op U)
  have hEF := (SemilinearSections.systemMap_existsUnique.{t + 1, t, max u (t + 1)}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l F W) (coefficientSequenceCommRingTransition l F W)
    (integralScalarQuotientSheafMap l E F (j.comp ι) W)
    (coefficientExtensionQuotient_naturality l E F (j.comp ι) W)).exists.choose_spec n (op U)
  change _ ≫ _ = _
  dsimp only [SemilinearSections.systemMap]
  rw [hEL, hLF, hEF]
  exact congrArg (fun z ↦ z.hom.app (op U)) (quotientSheaf_comp l E L ι W F j n)

/-- Existence of the balanced scalar association for three coefficient fields.
Source: integral scalar operations
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: on finite quotient sections send nested pure tensors to the product of
their two new coefficients and use insertion of one for the inverse. Quotient
naturality makes these maps coherent; the K-flat derived scalar comparison
then supplies the normalized derived equation. -/
theorem coefficientExtensionScalarAssociation_exists :
    Nonempty (CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) := by
  exact scalarAssociation_exists.{t + 1, t, u} A.scalar B.scalar D.scalar
    (systemMap_comp l E L ι W F j)

/-- The successive-extension comparison equation for a fixed association.
Source: integral operations (blueprint: lem-pur-coefficient-extension-reduction-model). -/
def CoefficientExtensionReductionCompositionEquation
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) : Prop :=
  ∀ K : DerivedCategory (scalarReductionSource l E W),
    (coefficientExtensionReductionIso l L F j W SL SF B dLF).hom.app
          ((integralScalarExtensionOfUniverses l E L ι W).obj K) ≫
        (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a).hom.app K =
      SF.reduction.map
          ((coefficientExtensionSuccessiveIso l E L ι W SE SL A F j SF
            B D dEL dLF dEF a).hom.app K) ≫
        (coefficientExtensionReductionIso l E F (j.comp ι) W SE SF D dEF).hom.app K

private theorem counit_comparison_comp
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D} {G : D ⥤ C}
    (adj : R ⊣ G) {X Z : D} {Y V : C} (x : Y ⟶ G.obj X)
    (e : G.obj Z ≅ V) (h : X ⟶ Z) :
    R.map x ≫ adj.counit.app X ≫ h =
      R.map (x ≫ G.map h ≫ e.hom) ≫ R.map e.inv ≫ adj.counit.app Z := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc e.hom e.inv, e.hom_inv_id, R.map_id, Category.id_comp]
  exact congrArg (fun f ↦ R.map x ≫ f) (adj.counit_naturality h).symm

/-- Counit naturality gives the successive-extension comparison equation for
a fixed balanced scalar association.
Source: integral scalar operations
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: use naturality of the coherent counit in the derived system category,
then substitute the successive system isomorphism and the three completion
identifications. The equality is obtained before evaluation, hence holds for
every derived object K. -/
theorem coefficientExtensionReductionCompositionEquation_proved
    (a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar) :
    CoefficientExtensionReductionCompositionEquation l E L ι W SE SL A F j SF B D
      dEL dLF dEF a := by
  intro K
  have h := counit_comparison_comp SF.adjunction
    (dLF.completion.inv.app ((integralScalarExtensionOfUniverses l E L ι W).obj K))
    (dEF.completion.app K)
    ((coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a).hom.app K)
  dsimp only [Iso.app_hom, Iso.app_inv] at h
  convert h using 1 <;>
    simp only [coefficientExtensionReductionIso, asIso_hom, coefficientExtensionCounit,
      coefficientExtensionSuccessiveIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.rightUnitor_hom_app, Functor.map_comp,
      Category.id_comp, Category.assoc]
  · erw [Category.id_comp]
  · erw [Category.comp_id]

/-- The direct and successive reduction comparisons agree as coherent system maps.
Source: integral operations, node proof steps 7--8
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: the ordinary associator and its inverse are balanced multiplication and
insertion of 1. They commute with every quotient transition; on three tensor factors
the two formulas multiply the same coefficients. K-flat change of rings and the
universal counits descend this strict association to coherent systems. Let h be
coefficientExtensionSuccessiveSystemIso. Naturality of the actual reduction/limit
counit gives h e_H = e_J R_F(L_F h). Substitute the normalized completion
identifications and the definitions of the three reduction comparisons. The
result is the displayed equation, before any evaluation. -/
theorem coefficientExtensionReduction_composition
    (_hl : IsUnit (l : Γ(W, ⊤))) :
    ∃ a : CoefficientScalarAssociation.{t + 1, t, u} A.scalar B.scalar D.scalar,
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        (coefficientExtensionReductionIso l L F j W SL SF B dLF).hom.app
            ((integralScalarExtensionOfUniverses l E L ι W).obj K) ≫
          (coefficientExtensionSuccessiveSystemIso l E L ι W SE SL A F j B D dEL a).hom.app K =
        SF.reduction.map
            ((coefficientExtensionSuccessiveIso l E L ι W SE SL A F j SF
              B D dEL dLF dEF a).hom.app K) ≫
          (coefficientExtensionReductionIso l E F (j.comp ι) W SE SF D dEF).hom.app K := by
  obtain ⟨a⟩ := coefficientExtensionScalarAssociation_exists
    (l := l) (E := E) (L := L) (ι := ι) (W := W) (A := A) (B := B) (D := D)
  refine ⟨a, ?_⟩
  exact coefficientExtensionReductionCompositionEquation_proved
    l E L ι W SE SL A F j SF B D dEL dLF dEF a
end SuccessiveExtension

/-- The actual identity coefficient inclusion induces identity on every quotient sheaf.
Source: the quotient construction in integral operations
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
private theorem quotientSheaf_id (n : ℕ) :
    integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W n = 𝟙 _ := by
  have hq : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n = RingHom.id _ := by
    ext x
    rfl
  unfold integralScalarQuotientSheafMap
  rw [hq]
  convert (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).map_id
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) using 1 <;> rfl

/-- Identity of the quotient maps gives identity of the actual sequence ring map.
Source: the componentwise specification of semilinear system maps
(blueprint: lem-pur-coefficient-extension-reduction-model). -/
private theorem systemMap_id :
    SemilinearSections.systemMap.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W)
      (coefficientExtensionQuotient_naturality l E E (AlgHom.id ℚ_[l] E) W) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rcases U with ⟨⟨n, U⟩⟩
  have h := (SemilinearSections.systemMap_existsUnique.{t + 1, t, max u (t + 1)}
    (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) W)
    (coefficientExtensionQuotient_naturality l E E (AlgHom.id ℚ_[l] E) W)).exists.choose_spec
      n (op U)
  exact h.trans (congrArg (fun f ↦ f.hom.app (op U)) (quotientSheaf_id l E W n))

/-- For identity extension, association is the action unitor and the comparison is
exactly the usual reduction counit of the completion. K need not be complete.
Source: integral operations, node proof step 6
(blueprint: lem-pur-coefficient-extension-reduction-model).
Proof: multiplication (x⊗a)⊗b ↦ x⊗ab is the action unitor when L=E.
Its localization has the stated universal-counit normalization. Naturality of the
coherent counit with this unitor gives the displayed equation. -/
theorem coefficientExtensionReduction_identity
    (A₀ : CoefficientExtensionSystems l E E (AlgHom.id ℚ_[l] E) W)
    (d : CoefficientExtensionReductionData l E E (AlgHom.id ℚ_[l] E) W SE SE A₀) :
    ∃ a : CoefficientScalarUnit.{t + 1, t, u} A₀.scalar,
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        (coefficientExtensionReductionIso l E E (AlgHom.id ℚ_[l] E) W SE SE A₀ d).hom.app K ≫
          (Functor.isoWhiskerLeft SE.reduction a.derived ≪≫
            Functor.rightUnitor SE.reduction).hom.app K =
        SE.reduction.map (d.completion.inv.app K ≫
          (coefficientSequenceLimit l E W).map
            ((Functor.isoWhiskerLeft SE.reduction a.derived ≪≫
              Functor.rightUnitor SE.reduction).hom.app K)) ≫
          SE.adjunction.counit.app (SE.reduction.obj K) := by
  obtain ⟨a⟩ := scalarUnit_exists A₀.scalar (systemMap_id l E W)
  refine ⟨a, ?_⟩
  intro K
  simp only [coefficientExtensionReductionIso, asIso_hom,
    coefficientExtensionCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Category.assoc]
  rw [Functor.map_comp, Category.assoc]
  congr 1
  dsimp only [coefficientExtensionSystem, Functor.comp_obj]
  erw [Category.id_comp, Category.comp_id]
  exact (SE.adjunction.counit.naturality (a.derived.hom.app (SE.reduction.obj K))).symm

end WeilConjectures
