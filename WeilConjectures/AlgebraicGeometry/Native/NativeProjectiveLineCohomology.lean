/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeCondensedDerivedComparison
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedProjectiveLineTensorDecomposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedTateFlat
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.ProjectiveLineCohomologyAlgebra
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Order.Basic

/-! # Native projective-line cohomology on a separated finite-type base -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale

private instance pointMod_preservesZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : ((upperStarFromPoint X).mapMod Λ).PreservesZeroMorphisms := by
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : (upperStarFromPoint X).PreservesZeroMorphisms := by
    unfold upperStarFromPoint
    infer_instance
  exact ⟨fun _ _ ↦ by ext; simp⟩

-- Zero is represented by the rank-zero presentation on the identity cover.
private theorem localModel_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

private theorem constructible_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : IsConstantModelConstructible Λ X (0 : Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  have hstrat (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hM : IsZero M) : IsFiniteConstantStratified Λ T M := by
    refine ⟨Scheme.Stratification.trivial T, fun a ↦ ?_⟩
    exact localModel_zero Λ _ _ ((CondensedRing.upperStar Λ _).map_isZero hM)
  classical
  unfold IsConstantModelConstructible
  split
  · exact hstrat X _ (isZero_zero _)
  · exact fun U _ ↦ hstrat _ _ ((CondensedRing.upperStar Λ U.ι).map_isZero (isZero_zero _))

set_option maxHeartbeats 1200000 in
-- The comparison involves several large exact-derived functor composites.
/-- Ordinary native projective-line cohomology has degree-zero sheaf M and vanishes
in positive degrees other than two on separated finite-type geometric bases.
Source: current blueprint, `thm-amb-p1-decomposition.proof.md`, tensor calculation.
(blueprint: lem-pur-native-projective-line-cohomology).

Proof: the normalized exact native/condensed equivalence preserves constructibility,
singles and cohomology and commutes with exact pullback and ordinary derived direct
image. Apply the condensed constant projective-line decomposition and the proper
projection formula to M[0]. The signed Tate line is flat by its compatible-root
trivialization, so its tensor with M[0] is in the heart. The shifted summand therefore
contributes only in degree two. Reflect the resulting cohomology isomorphism and zero
objects along the equivalence. Only an isomorphism of degree-zero objects is asserted;
no choice of an equivariant splitting is made.
-/
theorem native_projectiveLine_cohomology
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (hl : l ≠ ringChar k₀)
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hunit : IsUnit (l : Γ(S, ⊤))) (M : AdicSheaf l S)
    (hM : IsAdicConstructibleSheaf M) :
    Nonempty ((DerivedCategory.homologyFunctor _ 0).obj
        ((adicLowerStar l (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj
          ((adicUpperStar l (ProjectiveLine S ↘ S)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) ≅ M) ∧
      ∀ i : ℤ, 0 < i → i ≠ 2 →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((adicLowerStar l (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj
            ((adicUpperStar l (ProjectiveLine S ↘ S)).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
  let Λ := Profinite.padicAlgClRingObj l
  let E := nativeCondensedModules l S
  let N := E.obj M
  let B := (DerivedCategory.singleFunctor _ 0).obj N
  let q := ProjectiveLine S ↘ S
  let R := CondensedRing.moduleObjectDerivedPushforward Λ q
  let L := CondensedRing.moduleObjectDerivedPullback Λ q
  let K := (adicLowerStar l q).rightDerivedFunctor.obj
    ((adicUpperStar l q).mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M))
  have := (constantModelConstructibleFiniteTor_wellDefined Λ S).1
  have hN : IsConstantModelConstructible Λ S N :=
    nativeCondensed_constructible k₀ k l hl S M hM
  have hB : constantModelBoundedConstructible Λ S B := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
    by_cases hn : n = 0
    · subst n
      exact ObjectProperty.prop_of_iso _
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm hN
    · have hz : IsZero ((DerivedCategory.homologyFunctor _ n).obj B) := by
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact (DerivedCategory.isGE_iff B 0).mp inferInstance n hn
        · exact (DerivedCategory.isLE_iff B 0).mp inferInstance n hn
      exact ObjectProperty.prop_of_iso _
        ((isZero_zero _).iso hz) (constructible_zero Λ S)
  obtain ⟨ed⟩ := CondensedRing.exists_projectiveLine_tensor_decomposition l k S B
    (fun P _ h ↦ h B hB)
  let ep : E.mapDerivedCategory.obj K ≅ R.obj (L.obj B) :=
    (nativeCondensedDerivedPushforwardIso l q).some.app _ ≪≫
    R.mapIso ((nativeCondensedDerivedPullbackIso l q).some.app _ ≪≫
      L.mapIso ((E.mapDerivedCategorySingleFunctor 0).app M))
  obtain ⟨⟨e0⟩, hv⟩ := DerivedCategory.cohomology_single_biprod_flat_shift
    (tateTwist S l (-1)) N (CondensedRing.flat_tateTwist S l hunit (-1))
    (E.mapDerivedCategory.obj K) (ep ≪≫ ed)
  refine ⟨⟨E.preimageIso ((E.mapDerivedCategoryHomologyFunctorIso 0).app K ≪≫ e0)⟩,
    fun i hi hi2 ↦ ?_⟩
  exact E.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (hv i hi hi2)

end AlgebraicGeometry.ProEtale
