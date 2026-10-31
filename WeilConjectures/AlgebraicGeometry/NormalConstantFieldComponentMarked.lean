/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentMarkedLift
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentMarkedImmersion

/-! Marked-point and immersion data for the distinguished component.
(blueprint: lem-dl-a1-normal-constant-field-component-marked).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The selected tensor factor contains the marked point and is open and closed. -/
theorem normal_constant_field_component_marked
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left)
    (hη : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint
        ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 Z) :
    ∃ (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u})
      (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
      (j : C ⟶ (D.geometricFiber U₀).left),
      IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧
      j ≫ pullback.fst U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p ∧
      j ≫ pullback.snd U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s ∧
      (∃ ηC : Spec (CommRingCat.of Ω) ⟶ C, ηC ≫ j = η) ∧
      IsOpenImmersion j ∧ IsClosedImmersion j := by
  obtain ⟨σ, C, p, s, j, hpb, hp, hs, hηC⟩ :=
    normal_constant_field_component_marked_lift D U₀ b Ω η hη
  obtain ⟨ho, hc⟩ := normal_constant_field_component_marked_immersion
    D U₀ b Ω η hη σ C p s j hpb hp hs
  exact ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc⟩

end AlgebraicGeometry
