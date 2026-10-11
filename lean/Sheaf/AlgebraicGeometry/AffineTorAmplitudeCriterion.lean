/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Tor amplitude under the affine associated-sheaf correspondence

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.4, Tag 08E9,
part (1) (blueprint: lem-pc-affine-tor-amplitude-criterion).
-/

universe u wA wX

open CategoryTheory

namespace AlgebraicGeometry

/-- A module complex and its corresponding quasi-coherent derived object on `Spec A`
have the same Tor amplitude in `[a,b]`. The corresponding object is the image under `Q` of
the termwise tilde complex of `M`, as in `exists_affineQCohDerivedEquivalence`.
Source: Stacks Project, Tag 08E9, part (1)
(blueprint: lem-pc-affine-tor-amplitude-criterion).

Proof:
1. If the module complex has Tor amplitude `[a,b]`, choose a flat model concentrated
   in `[a,b]` using lem-pc-module-tor-amplitude-flat-model. Under
   lem-pc-affine-qcoh-derived-equivalence its associated-sheaf complex represents `E`.
   It is K-flat by lem-pc-affine-tilde-kflat. The tensor convention of
   lem-pc-affine-derived-pullback-tensor-tilde computes the derived tensor with every
   module sheaf by this ordinary tensor complex, which vanishes outside `[a,b]`.
2. Conversely, test sheaf Tor amplitude with the associated sheaf of every A-module N.
   Part (3) of lem-pc-affine-derived-pullback-tensor-tilde identifies this derived tensor
   with the associated sheaf complex of the module derived tensor. Tilde is exact:
   its stalks are localizations (lem-weil-pbc-spec-tilde-stalk-localization), and
   localization is exact. Thus it commutes with cohomology. It detects zero modules
   because global sections of tilde Q recover Q
   (lem-weil-pbc-affine-tilde-gamma-adjunction, part (2)). Vanishing of the sheaf
   cohomology therefore gives vanishing of the module cohomology outside `[a,b]`. -/
theorem affine_torAmplitude_iff (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b) :
    (∀ G : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes (Spec (.of A))
          (DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
              (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
              (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M))
          G i) ↔
      DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b (DerivedCategory.Q.obj M) := by
  sorry

end AlgebraicGeometry
