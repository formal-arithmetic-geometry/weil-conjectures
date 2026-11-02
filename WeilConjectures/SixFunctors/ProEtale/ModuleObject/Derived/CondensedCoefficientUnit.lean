/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
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
omit [IsCommMonObj Λ] in
private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj (0 : nativeModules Λ S)) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

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
