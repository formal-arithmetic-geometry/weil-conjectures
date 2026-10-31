/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedTowerRoos
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedProjectionAdjunction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerFiniteReduction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerDerivedComplete
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CofinalFiniteReductionConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CofinalCoefficientProjectionCocone
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.PoincareDuality.ScalarReductionCochainComparison
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # Complete objects as normalized ell-power tower limits

Source: latest blueprint, sec-smooth-purity, sk-lem-sp-tower-equivalence.proof.md.
(blueprint: lem-sp-completed-object-reconstruction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Every complete object is the limit of a normalized ell-power tower.
Source: current blueprint, sk-lem-sp-tower-equivalence.proof.md, Unit paragraph;
Bhatt--Scholze, Lemma 3.5.7 (blueprint: lem-sp-completed-object-reconstruction).

Proof: choose the actual strict reduction R and its independent, projection-normalized
ambient adjunction adj. For any normalized tower, the actual Roos triangle and the finite
projection-reduction theorem make each evaluated counit invertible. Conservative derived
system evaluations make the counit itself invertible. Put C = spCompletedReduction(R)(M).
The tower is normalized, and the left triangle identity shows that reduction sends
adj.unit.app M to an isomorphism.

Restriction along R.coefficient.hom is an exact equivalence, with inverse restriction along
R.coefficient.inv. Compose this equivalence's derived adjunction with the finite scalar
adjunction. The scalar-restriction composition comparison and left-adjoint uniqueness identify
evaluated completed reduction naturally with extension along each completed ell projection.
Thus all ell-power reductions of the unit are invertible.

Write ell = v*pi^e with e positive. For each n the canonical quotient from ell^(n+1) to
pi^(n+1) exists since n+1 <= e*(n+1). The completed projection cocone identifies its composite
with the specified uniformizer projection. Scalar composition therefore makes every uniformizer
reduction of the unit invertible. Compare the cochain scalar model with the prescribed finite
reduction, and apply the uniformizer calculus's conservative evaluations.

The actual total limit L(C) is intrinsically derived complete by the coefficient-tower limit
theorem. Its comparison with legacy completeness, using an auxiliary prime different from ell,
gives exactly the global slice completeness predicate. Uniformizer reconstruction makes the
units of its adjunction S at both M and L(C) invertible. Naturality gives
unit_ell(M) followed by unit_S(L(C)) equal to unit_S(M) followed by L_S(S(unit_ell(M))).
Every factor on the right is invertible. Cancel the invertible uniformizer unit to obtain the
invertibility of unit_ell(M). Its associated isomorphism supplies the witness. This imposes no
bounds and applies also to e=1, ramified extensions, zero objects and empty schemes. -/
theorem spCompletedObject_reconstruction
    [∀ x : T, Invertible (l : T.residueField x)]
    (D : SpCoefficientTowersAbelian l E T)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : WeilConjectures.IntegralOnSlice.IsComplete l E T none M) :
    ∃ C : spDerivedCoefficientTowers l E T D,
      IsSpNormalizedTower l E T D C ∧
        Nonempty (M ≅ (spCompletedTotalLimit l E T D).obj C) := by
  classical
  let := D.hasDerived
  let := D.equivalenceAdditive
  let : D.equivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let := WeilConjectures.integralOperationsDerivedCountableProducts l E T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨R⟩ := sp_reduction_tower_normalized l E T D
  obtain ⟨adj, hprojection⟩ := spCompletedReduction_projectionAdjunction l E T D R
  have hc (C : spDerivedCoefficientTowers l E T D)
      (hC : IsSpNormalizedTower l E T D C) : IsIso (adj.counit.app C) := by
    have heval (n : ℕ) :
        IsIso ((spDerivedCoefficientEvaluation l E T D n).map (adj.counit.app C)) := by
      obtain ⟨δ, hδ⟩ := spCompletedTotalLimit_roos l E T D C
      have := spTower_projection_finite_reduction l E T D C hC _ _ δ hδ n
      obtain ⟨e, he⟩ := hprojection C n
      rw [he]
      infer_instance
    have : IsIso (D.equivalence.mapDerivedCategory.functor.map (adj.counit.app C)) := by
      apply (SheafOfModules.systemDerivedEvaluation_isIso_iff
        (spCoefficientCommRings l E T) _).2
      intro n
      let := D.evaluationLimits n
      let := D.evaluationColimits n
      let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
        Functor.additive_of_preserves_binary_products _
      exact (NatIso.isIso_map_iff
        (Functor.mapDerivedCategoryCompIso D.equivalence.functor
          (SheafOfModules.systemEvaluation (spCoefficientCommRings l E T) n))
        (adj.counit.app C)).1 (heval n)
    exact isIso_of_reflects_iso (adj.counit.app C) D.equivalence.mapDerivedCategory.functor
  let C := (spCompletedReduction l E T D R).obj M
  have hC : IsSpNormalizedTower l E T D C := R.normalized _
  have hcC := hc C hC
  have hred : IsIso ((spCompletedReduction l E T D R).map (adj.unit.app M)) := by
    have h : IsIso ((spCompletedReduction l E T D R).map (adj.unit.app M) ≫
        adj.counit.app C) := by
      have ht : (spCompletedReduction l E T D R).map (adj.unit.app M) ≫
          adj.counit.app C = 𝟙 C := adj.left_triangle_components M
      rw [ht]
      exact CategoryTheory.IsIso.id C
    exact IsIso.of_isIso_comp_right _ (adj.counit.app C)
  have htransport (B : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
      (β : WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶ B) :
      (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          R.coefficient.hom)).mapDerivedCategory ⋙
        (D.scalar (R.coefficient.hom ≫ β)).model.T ≅ (D.scalar β).model.T := by
    let F := SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        R.coefficient.hom)
    let G := SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        R.coefficient.inv)
    let η : 𝟭 _ ≅ F ⋙ G :=
      (SheafOfModules.systemScalarRestrictionComposition R.coefficient.inv R.coefficient.hom
        (𝟙 _) R.coefficient.inv_hom_id.symm ≪≫
        SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1}
          (𝟙 (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)) rfl).symm
    let ε : G ⋙ F ≅ 𝟭 _ :=
      SheafOfModules.systemScalarRestrictionComposition R.coefficient.hom R.coefficient.inv
        (𝟙 _) R.coefficient.hom_inv_id.symm ≪≫
        SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1}
          (𝟙 (spIntegralSectionRing l E T)) rfl
    let e := CategoryTheory.Equivalence.mk F G η ε
    let : e.functor.Additive := inferInstanceAs F.Additive
    let : e.inverse.Additive := inferInstanceAs G.Additive
    let α := Functor.exactDerivedRestrictionComposition _ _ _
      (SheafOfModules.systemScalarRestrictionComposition R.coefficient.inv
        (R.coefficient.hom ≫ β) β (by simp))
    exact Adjunction.leftAdjointUniq
      ((e.mapDerivedCategory.toAdjunction.comp
        (D.scalar (R.coefficient.hom ≫ β)).adjunction).ofNatIsoRight α)
      (D.scalar β).adjunction
  have hell (n : ℕ) : IsIso
      ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.map (adj.unit.app M)) := by
    have he : spCompletedReduction l E T D R ⋙ spDerivedCoefficientEvaluation l E T D n ≅
        (D.scalar (spCompletedEllCommProjection l E T n)).model.T :=
      (Functor.associator _ _ _) ≪≫
        Functor.isoWhiskerLeft _ (R.evaluation n) ≪≫ htransport _ _
    exact (NatIso.isIso_map_iff he (adj.unit.app M)).mp (by
      change IsIso ((spDerivedCoefficientEvaluation l E T D n).map
        ((spCompletedReduction l E T D R).map (adj.unit.app M)))
      infer_instance)
  obtain ⟨e, v, he, hfactor⟩ := (sp_completed_coefficients_regular l E T).1
  obtain ⟨H, hH, _⟩ := sp_cofinal_coefficient_projection_cocone l E T e he v hfactor
  have hquot (n : ℕ) (hn : n + 1 ≤ e * (n + 1)) :
      spCompletedEllCommProjection l E T n ≫
        spCofinalFiniteCoefficientMap l E T e v hfactor n n hn =
      WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T n := by
    apply (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
    rw [Functor.map_comp]
    rw [show (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (spCompletedEllCommProjection l E T n) =
        (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
          limit.π (spCoefficientRings l E T) (op n) from Functor.map_preimage _ _]
    have hchoose : (sp_completed_coefficient_limit l E T).exists.choose =
        (sp_completed_coefficient_limit l E T).choose :=
      (sp_completed_coefficient_limit l E T).unique
        (sp_completed_coefficient_limit l E T).exists.choose_spec
        (sp_completed_coefficient_limit l E T).choose_spec.1
    rw [hchoose]
    convert (hH n n hn).2.2.2.1 using 1
    · rfl
    · ext U x
      rfl
  obtain ⟨S, _⟩ := WeilConjectures.coefficientDerivedSystemEvaluationCalculus l E T
  have hS : IsIso (S.reduction.map (adj.unit.app M)) := by
    apply (S.isIso_iff_evaluations _).mpr
    intro n
    have hn : n + 1 ≤ e * (n + 1) := by nlinarith
    let β := spCompletedEllCommProjection l E T n
    let γ := spCofinalFiniteCoefficientMap l E T e v hfactor n n hn
    let π := WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T n
    have hcomp : π = β ≫ γ := (hquot n hn).symm
    let i := SheafOfModules.systemScalarModelDerivedComposition hcomp
      (D.scalar β) (D.scalar γ) (D.scalar π)
    have := hell n
    have hi : IsIso ((D.scalar π).model.T.map (adj.unit.app M)) :=
      (NatIso.isIso_map_iff i (adj.unit.app M)).mp (by
        change IsIso ((D.scalar γ).model.T.map ((D.scalar β).model.T.map (adj.unit.app M)))
        infer_instance)
    obtain ⟨j⟩ := WeilConjectures.scalarReductionCochainModel_iso l E T n (D.scalar π).model
    have hj : IsIso ((WeilConjectures.coefficientFiniteDerivedExtension l E T n).map
        (adj.unit.app M)) := (NatIso.isIso_map_iff j (adj.unit.app M)).mp hi
    exact (NatIso.isIso_map_iff (S.reductionEvaluation n) (adj.unit.app M)).mpr hj
  have hcomplete : WeilConjectures.IntegralOnSlice.IsComplete l E T none
      ((spCompletedTotalLimit l E T D).obj C) := by
    obtain ⟨δ, hδ⟩ := spCompletedTotalLimit_roos l E T D C
    have hsf := spTower_limit_derived_complete l E T D C _ _ δ hδ
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let F : WeilConjectures.FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ F.p := by change l ≠ p; omega
    exact ⟨F, hl, (WeilConjectures.sfDerivedComplete_iff_legacy l E T F hl _).mp hsf⟩
  have hrec := (WeilConjectures.purNormalizedReconstructionOfScheme l E T S).2
  have := hrec M hM
  have := hrec ((spCompletedTotalLimit l E T D).obj C) hcomplete
  have : IsIso (adj.unit.app M ≫ S.adjunction.unit.app
      ((spCompletedTotalLimit l E T D).obj C)) := by
    have hn : adj.unit.app M ≫ S.adjunction.unit.app
        ((spCompletedTotalLimit l E T D).obj C) = S.adjunction.unit.app M ≫
        (S.reduction ⋙ WeilConjectures.coefficientSequenceLimit l E T).map
          (adj.unit.app M) := S.adjunction.unit.naturality (adj.unit.app M)
    rw [hn]
    change IsIso (S.adjunction.unit.app M ≫
      (WeilConjectures.coefficientSequenceLimit l E T).map
        (S.reduction.map (adj.unit.app M)))
    infer_instance
  have : IsIso (adj.unit.app M) := IsIso.of_isIso_comp_right _
    (S.adjunction.unit.app ((spCompletedTotalLimit l E T D).obj C))
  exact ⟨C, hC, ⟨asIso (adj.unit.app M)⟩⟩

end AlgebraicGeometry.ProEtale
