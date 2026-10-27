/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.AffineActionQuotientStack
public import Mathlib.AlgebraicGeometry.Stalk
public import Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # Completed local rings of schemes and their canonical maps

Source: Stacks, stacks-geometry.tex, Tag 0DQZ; etale.tex, Tag 039M
(blueprint: def-sfb-completed-local-scheme-chart).

The coefficient algebra comes from the structure morphism and the stalk map.
The morphism from the completed local spectrum uses the actual completion map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The closed residue point given by the specified residue-field identification.
Source: Stacks, Tag 0DQZ, residue-field convention
(blueprint: def-sfb-completed-local-scheme-chart). -/
def closedResiduePoint (Ω R : Type u) [Field Ω] [CommRing R] [IsLocalRing R]
    [Algebra Ω R] (ρ : IsLocalRing.ResidueField R ≃ₐ[Ω] Ω) :
    Over.mk (𝟙 (Spec (.of Ω))) ⟶ affineActionScheme Ω R :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (ρ.toRingHom.comp (IsLocalRing.residue R)))) (by
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp]
      have heq : CommRingCat.ofHom (algebraMap Ω R) ≫
          CommRingCat.ofHom (ρ.toRingHom.comp (IsLocalRing.residue R)) = 𝟙 _ := by
        ext a
        exact ρ.commutes a
      rw [heq, Spec.map_id])

/-- The actual local ring of a scheme over a field, completed at its maximal ideal,
with the field algebra structure induced by the structure morphism and the germ.
Source: Stacks, Tag 0DQZ and adic completion
(blueprint: def-sfb-completed-local-scheme-chart). -/
def pointCompletedLocalRing (Ω : Type u) [Field Ω]
    (T : Over (Spec (.of Ω))) (t : T.left) : CommAlgCat Ω :=
  let A := T.left.presheaf.stalk t
  letI : Algebra Ω A :=
    (Spec.preimage (T.left.fromSpecStalk t ≫ T.hom)).hom.toAlgebra
  letI : Algebra Ω (NodalFiber.completedLocalRing t) :=
    inferInstanceAs (Algebra Ω (AdicCompletion (IsLocalRing.maximalIdeal A) A))
  CommAlgCat.of Ω (NodalFiber.completedLocalRing t)

/-- The canonical map from the spectrum of the completed local ring to the scheme.
Its ring map is the completion map, followed contravariantly by the stalk map.
Source: Stacks, Tag 0DQZ
(blueprint: def-sfb-completed-local-scheme-chart). -/
def fromSpecPointCompletion (Ω : Type u) [Field Ω]
    (T : Over (Spec (.of Ω))) (t : T.left) :
    Spec (.of (pointCompletedLocalRing Ω T t)) ⟶ T.left :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (T.left.presheaf.stalk t)
      (AdicCompletion (IsLocalRing.maximalIdeal (T.left.presheaf.stalk t))
        (T.left.presheaf.stalk t)))) ≫ T.left.fromSpecStalk t


end AlgebraicGeometry
