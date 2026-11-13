/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.Dense

/-!
# Compactifications over a quasi-compact quasi-separated base
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every morphism between schemes over a quasi-compact, quasi-separated base,
with separated finite-type source and separated quasi-compact target over that base,
has a compactification with quasi-compact open immersion (Nagata). -/
theorem compactification_over_base {S X Y : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S]
    [IsSeparated (X ↘ S)] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [IsSeparated (Y ↘ S)] [QuasiCompact (Y ↘ S)] :
    Nonempty (Compactification.BoundaryCompactification f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ S)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ S)
  have : IsSeparated (f ≫ (Y ↘ S)) := by
    rw [comp_over f S]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ S)
  have : LocallyOfFiniteType (f ≫ (Y ↘ S)) := by
    rw [comp_over f S]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ S)
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  obtain ⟨c, _⟩ := exists_isDense_compactification f
  exact ⟨⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩⟩

end AlgebraicGeometry
