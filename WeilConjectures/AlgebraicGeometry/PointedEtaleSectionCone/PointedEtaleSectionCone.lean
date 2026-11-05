/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-! # Restriction along compatible sections of an initial pointed étale diagram

The colimit universal property constructs restriction for any compatible family of
sections above an initial diagram of pointed neighbourhoods. No strict-local model
is built into this construction.

Source: Stacks Project, Tag 03Q9, restriction from germs.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable {S T : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
  {s : Spec (.of Ω) ⟶ S} {I : Type v} [Category.{v} I]
  {N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements} {g : T ⟶ S}

namespace PointedEtaleSectionCone

variable (c : PointedEtaleSectionCone g N)

end PointedEtaleSectionCone

end AlgebraicGeometry.Etale
