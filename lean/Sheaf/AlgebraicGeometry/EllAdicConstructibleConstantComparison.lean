/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all Sheaf.Paper.ContinuousConstructibleIntegralTransport
import Sheaf.AlgebraicGeometry.EllAdicIntegralConstructibleConstantComparison

/-! # Comparison of adic constructibility predicates

Source: blueprint det-existence-restriction.proof.md, coefficient comparisons.
(blueprint: lem-sfb-adic-constructible-constant-comparison)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private lemma model_of_free_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hC : ∀ i : C.I₀, ∃ n : ℕ, Nonempty
      ((upperStar Λ (C.f i)).obj M ≅ Mod.finiteFree (condensedRingObj Λ (C.X i)) n)) :
    HasFiniteConstantLocalModel Λ X M := by
  classical
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC i
  refine ⟨Mod.finiteFree Λ n, ?_, ⟨e ≪≫ ?_⟩⟩
  · exact ⟨n, 0, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩
  · have : (upperStarFromPoint (C.X i)).IsLeftAdjoint :=
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (C.X i)))).isLeftAdjoint
    have : (upperStarFromPoint (C.X i)).Additive :=
      rightExactFunctor_le_additiveFunctor _ _ _ (by
        rw [rightExactFunctor_iff]
        infer_instance)
    have : ((upperStarFromPoint (C.X i)).mapMod Λ).Additive :=
      ⟨by intros; ext1; exact (upperStarFromPoint (C.X i)).map_add⟩
    exact ((upperStarFromPoint (C.X i)).mapMod Λ).mapBiproduct
      (fun _ : Fin n ↦ Mod.regular Λ) |>.symm

private lemma comparison_of_lfp_models (X : Scheme.{u}) [IsNoetherian X]
    (hm : ∀ (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
      (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)),
      IsLocallyFinitelyPresented (condensedRingObj Λ T) N → HasFiniteConstantLocalModel Λ T N)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    IsConstantModelConstructible Λ X M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  have : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  apply hm
  let φ := condensedPullbackHom Λ (S.immersion a)
  exact localFinitePresentation_of_iso ((Mod.extendScalarsIsoComapInv φ).app _).symm
    (localFinitePresentation_comap (inv φ) (hS a))

private theorem qbar_comparison (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M := by
  apply comparison_of_lfp_models (Profinite.padicAlgClRingObj ℓ) X _ M hM
  intro T _ N hN
  obtain ⟨C, hC⟩ := condensedQbar_lfp_locally_free ℓ T N hN
  exact model_of_free_cover _ N C hC

private theorem field_comparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E) X) M) :
    IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M := by
  apply comparison_of_lfp_models (Profinite.continuousMapRingObj E) X _ M hM
  intro T _ N hN
  obtain ⟨C, hC⟩ := smallField_finiteFree_cover ℓ E T N hN
  apply model_of_free_cover _ N C
  intro i
  let φ := condensedPullbackHom (Profinite.continuousMapRingObj E) (C.f i)
  have hh := ProEtale.free_comap (inv φ) (hC i)
  obtain ⟨n, ⟨e⟩⟩ := hh
  exact ⟨n, ⟨(Mod.extendScalarsIsoComapInv φ).app _ ≪≫ e⟩⟩


private lemma lfp_of_constant_model {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hC i
  have : (upperStarFromPoint (C.X i)).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (C.X i)))).isLeftAdjoint
  have : (upperStarFromPoint (C.X i)).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have hp := finitePresentation_mapMod (upperStarFromPoint (C.X i)) hP
  let φ := condensedPullbackHom Λ (C.f i)
  apply finitePresentation_of_iso _ (finitePresentation_comap φ hp)
  exact (Mod.comap φ).mapIso e.symm ≪≫
    (Mod.comap φ).mapIso ((Mod.extendScalarsIsoComapInv φ).app _) ≪≫
      (Mod.comapEquivalenceOfIsIso φ).counitIso.app _

private lemma constructible_of_constant {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsConstantModelConstructible Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at h
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun a ↦ ?_⟩
  have hp := lfp_of_constant_model Λ _ (hS a)
  let φ := condensedPullbackHom Λ (S.immersion a)
  have hp' := localFinitePresentation_comap φ hp
  exact localFinitePresentation_of_iso
    ((Mod.comap φ).mapIso ((Mod.extendScalarsIsoComapInv φ).app _) ≪≫
      (Mod.comapEquivalenceOfIsIso φ).counitIso.app _) hp'

/-- General and finite-constant-model constructibility agree for the three adic families.
Source: det-existence-restriction.proof.md, coefficient comparison, and the field,
algebraic-closure and integral local-presentation comparison nodes.
Proof: on each noetherian locally closed stratum use field local triviality for E,
its finite-subextension-valued counterpart for Qbar, or the integral constant-model
comparison for O_E. In the field cases finite free modules are inverse images of
finite powers of the regular condensed module; these have finite presentations.
Conversely inverse image preserves each finite scalar presentation; transport along
coefficient comparison isomorphisms gives precisely the general lfp predicate.
The empty scheme, zero ranks and integral torsion are included.
(blueprint: lem-sfb-adic-constructible-constant-comparison) -/
theorem ellAdic_constructible_constantModel
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M →
      IsConstantModelConstructible Λ X M := by
  cases hΛ with
  | continuous E => exact field_comparison ℓ E X M
  | integral E => exact ellAdic_integral_constructible_constantModel ℓ E X M
  | algebraicClosure => exact qbar_comparison ℓ X M

/-- The comparison is an equivalence; the reverse direction only uses finite
scalar presentations and the canonical coefficient pullback isomorphism. -/
theorem ellAdic_constructible_iff_constantModel
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
      IsConstantModelConstructible Λ X M :=
  ⟨ellAdic_constructible_constantModel Λ ℓ hΛ X M, constructible_of_constant Λ M⟩

end AlgebraicGeometry.ProEtale.CondensedRing
