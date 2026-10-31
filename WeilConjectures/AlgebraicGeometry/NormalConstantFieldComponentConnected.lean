/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic

/-! Connected-component range data for the distinguished component.
(blueprint: lem-dl-a1-normal-constant-field-component-connected).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The selected factor has the marked connected-component range and is connected. -/
theorem normal_constant_field_component_connected
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left)
    (hη : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint
        ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 Z)
    (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u})
    (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
    (j : C ⟶ (D.geometricFiber U₀).left)
    (hpb : IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)))
    (hp : j ≫ pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p)
    (hs : j ≫ pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s) :
    (∃ ηC : Spec (CommRingCat.of Ω) ⟶ C, ηC ≫ j = η) →
    IsOpenImmersion j → IsClosedImmersion j →
    Set.range j = connectedComponent
        ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 := by
  intro hηC ho hc
  let : ConnectedSpace C := b.geometricallyConnected.geometrically_connectedSpace _ _ _ hpb
  have hx : ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 ∈
      Set.range j := by
    obtain ⟨ηC, hηC⟩ := hηC
    change η (IsLocalRing.closedPoint Ω) ∈ Set.range j
    refine ⟨ηC (IsLocalRing.closedPoint Ω), ?_⟩
    exact congrArg (fun f : Spec (CommRingCat.of Ω) ⟶
      (D.geometricFiber U₀).left ↦ f (IsLocalRing.closedPoint Ω)) hηC
  apply Set.Subset.antisymm
  · exact (isConnected_range j.continuous).subset_connectedComponent hx
  · letI : IsOpenImmersion j := ho
    letI : IsClosedImmersion j := hc
    exact (show IsClopen (Set.range j) from
      ⟨j.isClosedMap.isClosed_range, j.isOpenEmbedding.isOpen_range⟩).connectedComponent_subset hx

end AlgebraicGeometry
