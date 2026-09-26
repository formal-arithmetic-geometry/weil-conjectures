/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The source of a proper morphism to a Noetherian scheme is Noetherian

`AlgebraicGeometry.isNoetherian_of_isProper` (Stacks Project Tag 01T6): a scheme proper over a
Noetherian scheme is Noetherian, since a proper morphism is locally of finite type (hence its
source is locally Noetherian) and quasi-compact (hence its source is quasi-compact).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **A scheme proper over a Noetherian scheme is Noetherian** (Stacks Project Tag 01T6). -/
theorem isNoetherian_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f] :
    IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

end AlgebraicGeometry
