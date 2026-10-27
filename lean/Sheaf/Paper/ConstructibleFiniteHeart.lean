/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import Sheaf.Paper.FiniteConstructibleComplexHeartPresentations
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-! # Constructible modules as finite constructible complex hearts -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

-- Step 1: use the identity cover and the zero finitely presented condensed module.
private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have (Y : Scheme.{u}) : (upperStarFromPoint Y).PreservesZeroMorphisms := by
    unfold upperStarFromPoint
    infer_instance
  have (Y : Scheme.{u}) : ((upperStarFromPoint Y).mapMod Λ).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)

/-- A constructible module is the heart of its complex concentrated in degree zero.
Source: the degree-zero complex construction in the finite-heart presentation definition.
(blueprint: lem-sfb-constructible-finite-heart)
Proof: take the complex with the supplied module in degree zero and zero elsewhere.
Its support is contained in the singleton zero. The zero module has the zero finite
scalar presentation and the one-stratum stratification, also on the empty scheme.
Transport constructibility across the degree-zero component isomorphism. Finally use
the canonical single-complex homology isomorphism. No coefficient or base finiteness
hypothesis enters. -/
theorem constructible_le_finiteConstructibleComplexHearts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    IsConstantModelConstructible Λ X ≤ finiteConstructibleComplexHearts Λ X := by
  intro N hN
  let B := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  refine ⟨(HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N, ⟨?_, ?_⟩,
    ⟨(HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N).symm⟩⟩
  · refine ⟨{0}, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa using hn)
  · intro n
    by_cases hn : n = 0
    · subst n
      exact constructible_iso (HomologicalComplex.singleObjXSelf _ _ _).symm hN
    · exact constantModelConstructible_of_isZero Λ X _
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

end AlgebraicGeometry.ProEtale
