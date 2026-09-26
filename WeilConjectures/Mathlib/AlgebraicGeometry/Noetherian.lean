/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Open subschemes of Noetherian schemes are Noetherian

`AlgebraicGeometry.isNoetherian_of_isOpenImmersion`: the source of an open immersion into a
Noetherian scheme is Noetherian. It is locally Noetherian by
`AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion`, and quasi-compact because every
subspace of a Noetherian space is compact.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- **The source of an open immersion into a Noetherian scheme is Noetherian.** -/
theorem isNoetherian_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsNoetherian Y] : IsNoetherian X :=
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion f
  have : CompactSpace X := by
    rw [← isCompact_univ_iff, f.isOpenEmbedding.isInducing.isCompact_iff]
    exact NoetherianSpace.isCompact _
  ⟨⟩

end AlgebraicGeometry
