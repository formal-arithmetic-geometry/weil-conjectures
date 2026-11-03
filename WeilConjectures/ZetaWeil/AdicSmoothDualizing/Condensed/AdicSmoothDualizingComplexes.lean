/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Adic and rational smooth dualizing complexes

Source: current blueprint, condensed coefficient corollary
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace WeilConjectures.AdicSmoothDualizing.Condensed

section UnitMembership
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
omit [IsCommMonObj Λ] in
private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj
      (0 : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X
      (0 : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

set_option maxHeartbeats 800000 in
-- The homology comparison elaborates through the internal module category.
/-- The coefficient sheaf in degree zero has a finite constant model.
Source: rational projective-line unit/counit proof step 5, rank-one scalar model
(blueprint: lem-sfb-rational-p1-line-from-preservation).
Proof: use the one-stratum partition and the identity cover. The scalar model is the
regular coefficient module, with its rank-one finite presentation. Monoidality of
inverse image identifies both pullbacks of this regular module. The single complex
is bounded, has this module as its zeroth cohomology and zero cohomology otherwise. -/
private theorem coefficientUnit_boundedConstructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) := by
  let C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
      (regular_constructible Λ X)
  · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact (DerivedCategory.isGE_iff _ 0).1 inferInstance n h
      · exact (DerivedCategory.isLE_iff _ 0).1 inferInstance n h
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((isZero_zero _).iso hz) (zero_constructible Λ X)


end UnitMembership

/-- The actual coefficient unit belongs to the native bounded constructible finite-Tor
category: its constant model is free of rank one and its Tor amplitude is [0,0].
Source: current corollary, coefficient-unit application
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
theorem unit_mem (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : property ell c X (unit ell c X) := by
  refine ⟨coefficientUnit_boundedConstructible (c.obj ell) X, 0, 0, ?_⟩
  intro N
  let e := tensorIso (DerivedCategory.singleFunctorObjUnitIso _) (Iso.refl
    ((DerivedCategory.singleFunctor _ 0).obj N)) ≪≫ λ_ _
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0⟩

end WeilConjectures.AdicSmoothDualizing.Condensed
