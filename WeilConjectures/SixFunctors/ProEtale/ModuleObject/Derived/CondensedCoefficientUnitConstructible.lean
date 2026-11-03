/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientObject
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # The coefficient unit belongs to the constructible finite-Tor category

Source: latest blueprint, the coefficient-unit input in the definition of the dualizing
complex (blueprint: lem-trf-coefficient-unit-ctf).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
omit [IsCommMonObj Λ] in
private theorem model_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj
      (0 : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) := by
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, zero_finitelyPresented Λ, ⟨?_⟩⟩
  exact ((CondensedRing.upperStar Λ (𝟙 X)).map_isZero
    ((CondensedRing.upperStar Λ f).map_isZero (isZero_zero _))).iso
      (((upperStarFromPoint X).mapMod Λ).map_isZero (isZero_zero _))

private theorem zero_constructible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstantModelConstructible Λ X
      (0 : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX]
  exact ⟨oneStratum X, fun _ ↦ model_zero Λ (𝟙 X)⟩

private theorem constructible_of_iso (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hlocal (Y : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : A ≅ B) (hA : HasFiniteConstantLocalModel Λ Y A) :
      HasFiniteConstantLocalModel Λ Y B := by
    obtain ⟨𝒰, h𝒰⟩ := hA
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ Y A) :
      IsFiniteConstantStratified Λ Y B := by
    obtain ⟨S, hS⟩ := hA
    exact ⟨S, fun a ↦ hlocal _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · exact hstrat _ e hM
  · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

set_option maxHeartbeats 800000 in
-- Homology comparisons elaborate through the internal module and derived tensor structures.
/-- The regular coefficient in degree zero is bounded constructible and has Tor interval
[0,0]. Source: the coefficient-unit input in the dualizing-complex definition
(blueprint: lem-trf-coefficient-unit-ctf).

Proof: the identity cover and one-stratum stratification give the constant scalar model
Lambda, finitely presented as the free module of rank one. The only nonzero cohomology of
its single complex is that regular module in degree zero; zero has the empty presentation.
The regular module is the tensor unit and is flat. Tensoring this single complex with
any module sheaf in degree zero returns that sheaf, so its Tor interval is [0,0]. -/
theorem constantCoefficientObject_mem
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)
      (constantCoefficientObject Λ X) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  change (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude C)
    ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))
  refine ⟨⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩, 0, 0, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      exact constructible_of_iso Λ X
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _).symm
        (regular_constructible Λ X)
    · have hz : IsZero ((DerivedCategory.homologyFunctor C n).obj
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))) := by
        rcases lt_or_gt_of_ne hn with h | h
        · exact (DerivedCategory.isGE_iff _ 0).1 inferInstance n h
        · exact (DerivedCategory.isLE_iff _ 0).1 inferInstance n h
      exact constructible_of_iso Λ X ((isZero_zero _).iso hz) (zero_constructible Λ X)
  · intro N
    let e := tensorIso (DerivedCategory.singleFunctorObjUnitIso C)
      (Iso.refl ((DerivedCategory.singleFunctor C 0).obj N)) ≪≫ λ_ _
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
      DerivedCategory.TStructure.t.isLE_of_iso e.symm 0⟩

end AlgebraicGeometry.ProEtale.CondensedRing
