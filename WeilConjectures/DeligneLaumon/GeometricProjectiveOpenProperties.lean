/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineGeometricallyIrreducible
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Geometry of a base-changed nonempty projective-line open -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

set_option maxHeartbeats 0 in
-- The base-change instances carry the explicit projective structural morphism.
/-- A nonempty open of a projective line, after field extension and an isomorphism,
is a connected regular Noetherian scheme.
Source: the projective-line charts and base change in the proof of
`lem-dl-a1-condensed-lisse-extension-kernel-forward`.
(blueprint: lem-dl-a1-geometric-projective-open-properties).

Proof: the open immersion followed by the projective structural map is smooth,
geometrically irreducible and quasi-compact. These properties survive field base change.
Smoothness over the new field gives regularity and local Noetherianity, while
quasi-compactness gives compactness. Geometric irreducibility over the field gives
connectedness. Transport the properties through the specified scheme isomorphism. -/
theorem geometric_projective_open_properties
    (k₀ k : Type u) [Field k₀] [Field k] [Algebra k₀ k]
    (W : (ProjectiveLine (Spec (.of k₀))).Opens) [Nonempty W]
    (X : Scheme.{u})
    (e : X ≅ pullback (W.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) :
    IsLocallyNoetherian X ∧ CompactSpace X ∧ ConnectedSpace X ∧ IsRegular X := by
  let f := W.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)
  let a := Spec.map (CommRingCat.ofHom (algebraMap k₀ k))
  have : Smooth f :=
    (ProjectiveLine.smoothOfRelativeDimension_one_of_isOpenImmersion W.ι).smooth
  have : GeometricallyIrreducible f :=
    ProjectiveLine.geometricallyIrreducible_of_isOpenImmersion W.ι
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k₀))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀))
  have : QuasiCompact f := by dsimp only [f]; infer_instance
  have : Smooth (pullback.snd f a) := inferInstance
  have : QuasiCompact (pullback.snd f a) := inferInstance
  have : IrreducibleSpace (pullback f a : Scheme.{u}) := inferInstance
  have : Smooth (e.hom ≫ pullback.snd f a) := inferInstance
  have : QuasiCompact (e.hom ≫ pullback.snd f a) := inferInstance
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (e.hom ≫ pullback.snd f a)
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (e.hom ≫ pullback.snd f a)
  have : ConnectedSpace X := (Scheme.homeoOfIso e).connectedSpace_iff.mpr inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance,
    IsRegular.of_smooth (e.hom ≫ pullback.snd f a)⟩

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
