/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # The coefficient unit is bounded constructible of Tor amplitude zero

Source: smooth-purity evaluation at the unit, Step 2 of thm-a1-curve-perverse-heart.
(blueprint: lem-per-condensed-coefficient-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private abbrev nativeModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

omit [IsCommMonObj Λ] in
private theorem regular_finitelyPresented : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  let e : Mod.finiteFree Λ 1 ≅ Mod.regular Λ := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree Λ 0)).symm⟩⟩

omit [IsCommMonObj Λ] in
private theorem zero_finitelyPresented : Mod.IsFinitelyPresented Λ (0 : Mod _ Λ) := by
  exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩

private instance pointBraided (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

private instance pointColimits (X : Scheme.{u}) :
    PreservesColimits (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

private instance pointAdditive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem model_regular {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨Mod.regular Λ, regular_finitelyPresented Λ, ⟨?_⟩⟩
  exact (CondensedRing.upperStar Λ (𝟙 X)).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm ≪≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (𝟙 X))).symm ≪≫
    Functor.Monoidal.εIso ((upperStarFromPoint X).mapMod Λ)

private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (0 : nativeModules Λ S)) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private def oneStratum (X : Scheme.{u}) : Scheme.Stratification X :=
  { n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := Set.iUnion_const _
    pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
    domain := fun _ ↦ X
    immersion := fun _ ↦ 𝟙 X
    range_immersion := fun _ ↦ Set.range_id' }

private theorem regular_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (Mod.regular (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_regular Λ (𝟙 X)⟩

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X (0 : nativeModules Λ X) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

set_option maxHeartbeats 800000 in
-- The homology comparison elaborates through the internal module category.
/-- The coefficient sheaf in degree zero has a finite constant model.
Source: the coefficient-unit assertion in proof step 1
(blueprint: lem-per-condensed-coefficient-unit).
Proof: use the one-stratum partition and the identity cover. The scalar model is the
regular coefficient module, with its rank-one finite presentation. Monoidality of
inverse image identifies both pullbacks of this regular module. The single complex
is bounded, has this module as its zeroth cohomology and zero cohomology otherwise. -/
private theorem coefficientUnit_boundedConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X
      ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
        (Mod.regular (condensedRingObj Λ X))) := by
  let C := nativeModules Λ X
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible Λ X)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
        ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
          (Mod.regular (condensedRingObj Λ X)))) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
        (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff ((DerivedCategory.singleFunctor (nativeModules Λ X) 0).obj
        (Mod.regular (condensedRingObj Λ X))) 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible Λ X)

/-- The derived unit is the regular module in degree zero. Its tensor with
any degree-zero module is that module, so the Tor interval is [0,0]. -/
theorem condensedCoefficientUnit_mem (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)
      (𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))) := by
  let C := nativeModules Λ X
  have hb := coefficientUnit_boundedConstructible Λ X
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  refine ⟨(constantModelBoundedConstructible Λ X).prop_of_iso
    (DerivedCategory.singleFunctorObjUnitIso C) hb, 0, 0, ?_⟩
  intro N
  exact (DerivedCategory.homologyConcentratedIn 0 0).prop_of_iso
    (λ_ ((DerivedCategory.singleFunctor C 0).obj N)).symm
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale.CondensedRing
