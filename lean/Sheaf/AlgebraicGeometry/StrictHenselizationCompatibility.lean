/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Compatibility corollaries for the upstream strict henselization

These corollaries preserve the helper API of retired SHEAF modules for worker deliveries
created before the upstream sync. The ring, scheme, and local structure are upstream's.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The affine pointed inclusion is initial and its opposite is final, by upstream cofinality. - /
theorem affinePointedNeighbourhoods_initial_and_final_op
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Functor.Initial
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)) ∧
    Functor.Final
      (ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).op := by
  sorry
-/

end Scheme

/-- Upstream's henselian local ring and separably closed residue field give strict henselianity. -/
theorem strictHenselizationLocalStructure
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselizationRing barY) := by
  sorry

end AlgebraicGeometry
