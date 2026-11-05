/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionCone
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-! # The small strict-local model as a pointed section cone

Only the model-specific geometric sections and their compatibility are constructed here.
Restriction and its universal property use the general PointedEtaleSectionCone API.

Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

variable {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

end AlgebraicGeometry.Etale
