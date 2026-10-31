/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentMarked
import WeilConjectures.AlgebraicGeometry.NormalConstantFieldComponentConnected

/-! Construction of the distinguished clopen constant-field component.

Source: Stacks Project, varieties.tex, Tags 04PZ, 054Q and 0C3M; fields.tex, Tag 0CKN.
(blueprint: lem-dl-a1-normal-constant-field-component-construction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The finite tensor decomposition constructs the clopen connected component through a
specified geometric generic point, together with its pullback and projection data.

Source: Stacks Project, fields.tex, Tag 0CKN; varieties.tex, Tags 054Q and 0C3M.
(blueprint: lem-dl-a1-normal-constant-field-component-construction).

Proof: choose the embedding of the finite constant field induced by the geometric point.
The finite Galois tensor decomposition, extended to the algebraically closed field, gives
clopen affine factors on every affine chart.  These factors glue to the pullback component;
the marked point lies in the distinguished factor.  Geometric connectedness identifies that
factor with the connected component of the point.
-/
theorem normal_constant_field_component_construction
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
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
      IsOpenImmersion j ∧ IsClosedImmersion j ∧
      Set.range j = connectedComponent
        ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 ∧
      ConnectedSpace C := by
  obtain ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc⟩ :=
    normal_constant_field_component_marked D U₀ b Ω η hη
  let : ConnectedSpace C := b.geometricallyConnected.geometrically_connectedSpace _ _ _ hpb
  obtain hrange := normal_constant_field_component_connected
    D U₀ b Ω η hη σ C p s j hpb hp hs hηC ho hc
  exact ⟨σ, C, p, s, j, hpb, hp, hs, hηC, ho, hc, hrange, inferInstance⟩

end AlgebraicGeometry
