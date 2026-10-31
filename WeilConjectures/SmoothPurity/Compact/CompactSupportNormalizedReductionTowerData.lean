/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition

/-! # Finite compact-support normalized tower data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientSequenceTransition constantSheaf
  Padic.coefficientExtensionIdeal compactSupportOrdinaryCoefficientTransition

/-- The finite compact-support terms admit a normalized tower and compatible level
isomorphisms.  This is the construction and transition part of the compact-support
normalization argument, before the independent constructibility and boundedness claim.
Source: current blueprint `lem-fix-operation-reduction.proof.md`, compact-support
paragraph; Bhatt--Scholze Lemmas 6.7.7 and 6.8.14; Stacks Tags 08J9 and 0FPT.
The proof chooses flat-term K-flat representatives, identifies finite quotient
reductions by the two-term free resolutions, and transports the scalar-adjunction
mates through extension by zero and proper direct image.  Coherence of these mates
assembles the normalized tower and gives the displayed adjacent transition square.
The construction works for identity and zero levels and never invokes an inverse
limit or a projection comparison.
(blueprint: lem-sf-compact-support-normalized-reduction-tower-data). -/
theorem compactSupport_normalizedReductionTower_data
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ (T : NormalizedDVRTower l E Y D hl)
      (a : ∀ n : ℕ, T.M n ≅
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
          ((scalarReductionDerivedExtension l E X n).obj K)),
      ∀ n : ℕ,
        (normalizedDVRTowerTransition l E Y D hl n.le_succ).app T.tower ≫
            (T.evaluationIso n ≪≫
              (scalarReductionDerivedRestriction l E Y n).mapIso (a n)).hom =
          (T.evaluationIso (n + 1) ≪≫
              (scalarReductionDerivedRestriction l E Y (n + 1)).mapIso (a (n + 1))).hom ≫
            sfCompactSupportTransition l E c K n := by
  classical
  obtain ⟨S, _hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E X
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K)
  let T : NormalizedDVRTower l E Y D hl := {
    M := fun n ↦ (coefficientSequenceDerivedEvaluation l E Y n).obj N
    tau := fun h ↦ (coefficientSequenceDerivedTransition l E Y h).app N
    tau_refl := derivedTransition_id l E Y N
    tau_comp := fun h₁ h₂ ↦ derivedTransition_comp l E Y N h₁ h₂
    tower := (coefficientSequenceDerivedRestriction l E Y).obj N
    evaluationIso := fun n ↦ (coefficientRestrictedEvaluationIso l E Y n).app N
    tower_tau := fun h ↦ derivedRestrictedTransition l E Y D hl N h
    normalization := compactSupportSystem_normalized l c K₀ hl₀ E ⟨K, hK⟩ S }
  let F (j : ℕ) := sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E (j + 1))
  let e (j : ℕ) : (coefficientSequenceDerivedEvaluation.{u, u} l E Y j).obj N ≅
      (F j).obj ((scalarReductionDerivedExtension l E X j).obj K) :=
    (compactSupportSystemEvaluation l E c j).app (S.reduction.obj K) ≪≫
      (F j).mapIso ((S.reductionEvaluation j).app K)
  refine ⟨T, e, ?_⟩
  intro j
  let r (W : Scheme.{u}) := (proEtaleCoefficientRestrictScalars W
    (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).mapDerivedCategory
  let ε (i : ℕ) := (compactSupportSystemEvaluation l E c i).hom.app (S.reduction.obj K)
  let ρ (i : ℕ) := (S.reductionEvaluation i).hom.app K
  have H := compactSupportFiniteSquare (F (j + 1)) (F j) (r X) (r Y)
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).hom
    _ _ _ _ _ _ _
    (compactSupportNativeSystemTransition l E c j.le_succ (S.reduction.obj K))
    (compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction j.le_succ K)
  have H' := compactSupportCompletedSquare (r Y)
    (scalarReductionDerivedRestriction l E Y (j + 1))
    (scalarReductionDerivedRestriction l E Y j)
    (compactSupportRestrictionComp l E Y (j + 1) j j.le_succ).hom
    ((compactSupportCoefficientTransition l E Y j.le_succ).app N)
    (ε (j + 1)) (ε j) ((F (j + 1)).map (ρ (j + 1))) ((F j).map (ρ j))
    ((F (j + 1)).map (compactSupportReductionMap l E X (j + 1) j j.le_succ K))
    ((sfCompactSupportRestriction c
      (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).hom.app
        ((scalarReductionDerivedExtension l E X j).obj K))
    ((pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
      (j + 1) j j.le_succ).app T.tower)
    ((coefficientRestrictedEvaluationIso l E Y (j + 1)).hom.app N)
    ((coefficientRestrictedEvaluationIso l E Y j).hom.app N)
    (compactSupportCoefficientTransition_restricted l E Y j.le_succ N) H
  change (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
    (j + 1) j j.le_succ).app T.tower ≫ _ = _
  simpa only [T, e, ε, ρ, sfCompactSupportTransition, sfCompactSupportTerm,
    Nat.succ_eq_add_one, adjacentReductionMap, adjacentRestrictionComp, adjacentQuotient,
    compactSupportLevelQuotient, Padic.coefficientExtensionTransition,
    coefficientFiniteDerivedExtension, sfIntrinsicCompactSupport,
    sfAmbientCompactSupportCandidate, F,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using H'

end WeilConjectures
