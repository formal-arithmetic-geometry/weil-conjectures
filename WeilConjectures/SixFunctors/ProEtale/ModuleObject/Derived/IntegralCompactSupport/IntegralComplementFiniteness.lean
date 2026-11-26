/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Integral finiteness for the open term of localization
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

private theorem constructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
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
  rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  refine ⟨S, fun a ↦ ?_⟩
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun b ↦ ?_⟩
  let P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ :=
    cokernel (𝟙 (Mod.finiteFree Λ 0))
  refine ⟨P, ⟨0, 0, 𝟙 _, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  have : pointUpperStar.{u}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : (upperStarFromPoint X).PreservesZeroMorphisms := by
    unfold upperStarFromPoint
    infer_instance
  have : ((upperStarFromPoint X).mapMod Λ).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  exact (((upperStar Λ (S.immersion a)) ⋙ (upperStar Λ (𝟙 X))).map_isZero hM).iso
    (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_cokernel_of_epi _))

private theorem generators_triangulated
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    (generators (Profinite.padicIntegersRingObj ℓ E.val) X).IsTriangulated := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := IsConstantModelConstructible Λ X
  obtain ⟨hkc, hext⟩ := isConstantModelConstructible_serre_padicIntegers X ℓ E
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  let : Zero (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := HasZeroObject.zero' _
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, constructible_of_isZero Λ X _ (isZero_zero _)⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, c, hc, h⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hc)
      (hkc _ _ f h.1 h.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, c, hc, h⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc)
      (hkc _ _ f h.1 h.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ hext _ hS h1 h3⟩
  change (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P).IsTriangulated
  rw [inf_comm]
  exact (cohomology_in_weak_serre_subcategory P).2.2

/-- The integral constructible class is triangulated, and the open-complement term of
localization belongs to it. This assertion concerns inverse image and open direct image;
it involves neither sections with closed support nor a Brown adjoint.
-/
theorem integralComplementFiniteness
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (generators (Profinite.padicIntegersRingObj ℓ E.val) X).IsTriangulated ∧
      ∀ K, generators (Profinite.padicIntegersRingObj ℓ E.val) X K →
        generators (Profinite.padicIntegersRingObj ℓ E.val) X
          (((upperStar (Profinite.padicIntegersRingObj ℓ E.val)
            i.openComplement.ι).mapDerivedCategory ⋙
              (lowerStar (Profinite.padicIntegersRingObj ℓ E.val)
                i.openComplement.ι).rightDerivedFunctor).obj K) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  refine ⟨generators_triangulated ℓ E X, ?_⟩
  let U := i.openComplement.toScheme
  let j : U ⟶ X := i.openComplement.ι
  let : U.Over (Spec (.of k)) := ⟨j ≫ X ↘ Spec (.of k)⟩
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (j ≫ X ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (U ↘ Spec (.of k)) := by
    change QuasiCompact (j ≫ X ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (U ↘ Spec (.of k)) := by
    change IsSeparated (j ≫ X ↘ Spec (.of k))
    infer_instance
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U :=
    QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  intro K hK
  have hJ := (integralModels_operations ℓ E).1 j K hK
  have hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E'.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E'.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
    Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩))
  have heq := (localizingClosure_ctf_equals_bc ℓ U Λ hΛ).1.2.2.1
  have hJT : (constantModelBoundedConstructible Λ U ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) ((upperStar Λ j).mapDerivedCategory.obj K) := by
    rw [heq]
    exact hJ
  exact (integralOpenDirectImage ℓ E k j ⟨_, hJT⟩).1

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
