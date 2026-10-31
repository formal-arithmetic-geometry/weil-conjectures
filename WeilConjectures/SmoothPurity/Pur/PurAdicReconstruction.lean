/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.Adic.AdicPurityExceptionalReduction
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceFiniteness
import all WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicNormalizedPurityLift
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
/-! # Adic reconstruction of the specified finite smooth-purity comparisons
Source: blueprint thm-pur-adic-reconstruction, current main-20261015 snapshot.
The source is integral pullback followed by the actual coefficient twist and shift.
The target is the total inverse limit of the actual exceptional coefficient system.
All finite coefficients are those of PurityFiniteSetting.{u}, without a universe lift
of the geometric datum or a divisibility restriction on the coefficient exponent.
(blueprint: thm-pur-adic-reconstruction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] purAdicExceptionalEvaluation
  scalarReductionExistence scalarReductionDerivedExistence

/-- Exact restriction/evaluation comparison induced by the ordinary identity on sections.
Source: blueprint strict tower realization (blueprint: thm-pur-adic-reconstruction). -/
def purAdicRestrictedEvaluation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) (n : ℕ) :
    coefficientSequenceDerivedRestriction l E W ⋙ coefficientConstantTowerEvaluation l E W n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        (scalarReductionRestriction l E W n).mapDerivedCategory :=
  letI := scalarReductionRestrictionLimits l E W n
  letI := scalarReductionRestrictionColimits l E W n
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem completionUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (hl : IsUnit (l : Γ(W, ⊤)))
    (P : DerivedCategory (scalarReductionSource l E W))
    (hP : sfIntegralConstructible l E W P) :
    IsIso ((pullbackTensorCalculus l E W).adjunction.unit.app P) := by
  let S := pullbackTensorCalculus l E W
  let T := purCoefficientModel l E W
  let M := T.inverse.obj P
  have hm : sfIntegralConstructible l E W (T.functor.obj M) :=
    (sfIntegralConstructible l E W).prop_of_iso (T.counitIso.app P).symm hP
  have hp := purCoefficientModel_predicates l E W M
  have hc := hp.1.mp (hp.2.mpr hm.1)
  have hi := (purNormalizedReconstruction l E W hl S).2 _ hc
  have hn := S.adjunction.unit.naturality (T.counitIso.app P).hom
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  have : IsIso (S.adjunction.unit.app (T.functor.obj M)) := hi
  have : IsIso ((T.counitIso.app P).hom ≫ S.adjunction.unit.app P) := by
    exact hn ▸ (inferInstance : IsIso (S.adjunction.unit.app (T.functor.obj M) ≫
      (S.reduction ⋙ coefficientSequenceLimit l E W).map (T.counitIso.app P).hom))
  exact (isIso_comp_left_iff (T.counitIso.app P).hom _).mp inferInstance

private theorem finiteTorIntegral_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    {P Q : DerivedCategory (scalarReductionSource l E W)} (e : P ≅ Q)
    (hP : finiteTorConstructibleIntegral l E W P) :
    finiteTorConstructibleIntegral l E W Q := by
  refine ⟨(sfIntegralConstructible l E W).prop_of_iso e hP.1, ?_⟩
  obtain ⟨a, b, hab, h⟩ := hP.2
  refine ⟨a, b, hab, fun n ↦ ⟨(h n).1, ?_⟩⟩
  intro N R hN f hf hR M i hi
  exact (h n).2 N R
    (hN.map fun q ↦ q ≪≫ ((scalarReductionDerivedExtension l E W n).mapIso e).symm)
    f hf hR M i hi

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

set_option maxHeartbeats 800000 in
-- The scalar-adjunction calculation compares the concrete derived coefficient presentations.
/-- Adic reconstruction of the specified finite smooth-purity arrows.
Source: blueprint thm-pur-adic-reconstruction, current statement and five-step proof
(blueprint: thm-pur-adic-reconstruction).
Proof: integral pullback and the locally free coefficient twist give the actual source,
its uniform constructible and Tor bounds, and its canonical quotient identifications.
Evaluate the strict exceptional system, using the section-normalized site comparisons
and the compact-support adjunction mates, to obtain the actual finite exceptional images.
The finite purity arrows commute with quotient normalization by finite reduction of
purity. After exact scalar restriction, sequential-tower evaluation fullness supplies a
coherent morphism G with the displayed evaluations; no uniqueness of G is asserted.
Take its total derived inverse limit and precompose the derived-completion unit of the
source. The level arrows are isomorphisms by isIso_smoothPurityMap. The natural Roos
triangles then make this limit map invertible. Source finiteness and isomorphism
invariance give target finiteness. Normalized DVR effectivity identifies the target
reduction counits as isomorphisms. Transposing the limit-projection equation under
actual derived scalar extension/restriction proves the displayed quotient-linear
identity, rather than merely asserting that some reduced map is invertible. -/
theorem purAdicReconstruction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    ∃ gamma : purAdicSource D C E f d K ⟶ purAdicTarget D C E f K,
      IsIso gamma ∧
      finiteTorConstructibleIntegral C.l E X (purAdicSource D C E f d K) ∧
      finiteTorConstructibleIntegral C.l E X (purAdicTarget D C E f K) ∧
      (∀ n : ℕ, IsIso (purAdicSourceReduction D C E f d K hK n) ∧
        IsIso (purAdicTargetReduction D C E f d K hK n) ∧
        (scalarReductionDerivedExtension C.l E X n).map gamma ≫
          purAdicTargetReduction D C E f d K hK n =
        purAdicSourceReduction D C E f d K hK n ≫
          (purAdicFiniteArrow D C E f d K hK n).hom) ∧
      ∃ G : (coefficientSequenceDerivedRestriction C.l E X).obj
          ((pullbackTensorCalculus C.l E X).reduction.obj (purAdicSource D C E f d K)) ⟶
        (coefficientSequenceDerivedRestriction C.l E X).obj
          ((integralExceptionalSystem C.l E D C.different f).obj K),
        gamma = (pullbackTensorCalculus C.l E X).adjunction.unit.app _ ≫
          (coefficientConstantTowerLimit C.l E X).map G ∧
        ∀ n : ℕ,
          (coefficientConstantTowerEvaluation C.l E X n).map G ≫
            (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
            (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
              (purAdicExceptionalEvaluation D C E f K n).hom =
          (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
            (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
              (((pullbackTensorCalculus C.l E X).reductionEvaluation n).hom.app _ ≫
                purAdicSourceReduction D C E f d K hK n ≫
                (purAdicFiniteArrow D C E f d K hK n).hom) := by
  classical
  let S := pullbackTensorCalculus C.l E X
  let U : DerivedCategory (scalarReductionSource C.l E X) := purAdicSource D C E f d K
  let N := (integralExceptionalSystem C.l E D C.different f).obj K
  have hsource := purAdicSource_finiteness_reductions D C E f d K hK
  have hU := hsource.1
  have hb := hsource.2.2.1
  have hlift := AdicNormalizedPurity.normalized_purity_lift D C E f d K hK
  have hg := hlift.1
  obtain ⟨G, hG⟩ := hlift.2.2.2.2
  have hG' (n : ℕ) :
      (coefficientConstantTowerEvaluation C.l E X n).map G ≫
        (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
        (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
          (purAdicExceptionalEvaluation D C E f K n).hom =
      (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
        (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
          ((S.reductionEvaluation n).hom.app U ≫
            purAdicSourceReduction D C E f d K hK n ≫
            (purAdicFiniteArrow D C E f d K hK n).hom) := by
    have he := hG n
    dsimp only [AdicNormalizedPurity.sourceEvaluation,
      AdicNormalizedPurity.targetEvaluation, Iso.trans_hom, Functor.mapIso_hom] at he
    with_unfolding_all
      change (coefficientConstantTowerEvaluation C.l E X n).map G ≫
          (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            (purAdicExceptionalEvaluation D C E f K n).hom =
        ((purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            ((S.reductionEvaluation n).hom.app U ≫
              purAdicSourceReduction D C E f d K hK n)) ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            (purAdicFiniteArrow D C E f d K hK n).hom at he
    simpa only [Functor.map_comp, Category.assoc] using he
  have hEval (n : ℕ) : IsIso ((coefficientConstantTowerEvaluation C.l E X n).map G) := by
    let := hb n
    let := hg n
    have : IsIso ((coefficientConstantTowerEvaluation C.l E X n).map G ≫
        (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
        (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
          (purAdicExceptionalEvaluation D C E f K n).hom) := by
      rw [hG' n]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((coefficientConstantTowerEvaluation C.l E X n).map G)
      ((purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
        (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
          (purAdicExceptionalEvaluation D C E f K n).hom)
  have hGI : IsIso G := by
    rw [DerivedCategory.isIso_iff]
    intro j
    let : ∀ n : ℕᵒᵖ,
        IsIso (((DerivedCategory.homologyFunctor _ j).map G).app n) := fun n ↦ by
      have := hEval n.unop
      let V := (CategoryTheory.evaluation ℕᵒᵖ
        (scalarReductionSource C.l E X)).obj n
      exact (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso j) G).2
        (show IsIso ((DerivedCategory.homologyFunctor _ j).map
          ((coefficientConstantTowerEvaluation C.l E X n.unop).map G)) from inferInstance)
    exact NatIso.isIso_of_isIso_app _
  have hunit : IsIso (S.adjunction.unit.app U) :=
    completionUnit_isIso C.l E X (purAdicCoefficientUnit D C X) U hU.1
  let gamma : U ⟶ purAdicTarget D C E f K :=
    S.adjunction.unit.app U ≫ (coefficientConstantTowerLimit C.l E X).map G
  have hgamma : IsIso gamma := by
    dsimp only [gamma]
    infer_instance
  have heq (n : ℕ) :
      (scalarReductionDerivedExtension C.l E X n).map gamma ≫
        purAdicTargetReduction D C E f d K hK n =
      purAdicSourceReduction D C E f d K hK n ≫
        (purAdicFiniteArrow D C E f d K hK n).hom := by
    let a := coefficientFiniteAdjunction C.l E X n
    let R := coefficientFiniteDerivedRestriction C.l E X n
    let b := purAdicSourceReduction D C E f d K hK n
    let g := (purAdicFiniteArrow D C E f d K hK n).hom
    let t := (purAdicExceptionalEvaluation D C E f K n).hom
    dsimp only [purAdicTargetReduction]
    apply (a.homEquiv U _).injective
    change (a.homEquiv U _)
      ((coefficientFiniteDerivedExtension C.l E X n).map gamma ≫
        (S.reductionEvaluation n).inv.app _ ≫
          (coefficientSequenceDerivedEvaluation C.l E X n).map
            (S.adjunction.counit.app N) ≫ t) =
      (a.homEquiv U _) (b ≫ g)
    with_unfolding_all
      rw [a.homEquiv_naturality_left]
      change gamma ≫ (a.homEquiv _ _)
        ((S.reductionEvaluation n).inv.app ((coefficientSequenceLimit C.l E X).obj N) ≫
          (coefficientSequenceDerivedEvaluation C.l E X n).map
            (S.adjunction.counit.app N) ≫ t) = (a.homEquiv U _) (b ≫ g)
      rw [← Category.assoc ((S.reductionEvaluation n).inv.app _)
        ((coefficientSequenceDerivedEvaluation C.l E X n).map
          (S.adjunction.counit.app N)) t]
      rw [a.homEquiv_naturality_right]
    erw [S.counit_projection N n]
    rw [Adjunction.homEquiv_unit]
    change gamma ≫ (coefficientSequenceProjection C.l E X n).app N ≫ R.map t =
      a.unit.app U ≫ R.map (b ≫ g)
    have hn := (coefficientConstantTowerProjection C.l E X n).naturality G
    calc
      gamma ≫ (coefficientSequenceProjection C.l E X n).app N ≫ R.map t =
          S.adjunction.unit.app U ≫
            (coefficientSequenceProjection C.l E X n).app (S.reduction.obj U) ≫
            R.map ((S.reductionEvaluation n).hom.app U ≫ b ≫ g) := by
        dsimp only [gamma, coefficientSequenceProjection, NatTrans.comp_app,
          Functor.whiskerLeft_app]
        simp only [Category.assoc]
        erw [reassoc_of% hn]
        erw [hG' n]
        with_unfolding_all rfl
      _ = a.unit.app U ≫ R.map (b ≫ g) := by
        rw [← Category.assoc, S.unit_projection]
        simp only [Category.assoc, Functor.map_comp]
        rw [← Functor.map_comp_assoc]
        simp only [Iso.inv_hom_id_app]
        with_unfolding_all
          rw [(coefficientFiniteDerivedRestriction C.l E X n).map_id]
          rw [Category.id_comp]
  refine ⟨gamma, hgamma, hU, finiteTorIntegral_iso C.l E X (asIso gamma) hU,
    fun n ↦ ?_, G, rfl, hG'⟩
  let := hb n
  let := hg n
  have : IsIso ((scalarReductionDerivedExtension C.l E X n).map gamma ≫
      purAdicTargetReduction D C E f d K hK n) := by
    rw [heq n]
    infer_instance
  refine ⟨hb n, ?_, heq n⟩
  exact IsIso.of_isIso_comp_left
    ((scalarReductionDerivedExtension C.l E X n).map gamma)
    (purAdicTargetReduction D C E f d K hK n)

end WeilConjectures
