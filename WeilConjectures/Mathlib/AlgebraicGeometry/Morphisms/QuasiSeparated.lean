/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasi-compactness of the inclusion of a preimage open

The inclusion of the preimage of a quasi-compact open under a quasi-compact morphism from
a quasi-separated scheme is quasi-compact
(`AlgebraicGeometry.quasiCompact_preimage_ι`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `g : P ⟶ X` is quasi-compact, `P` is quasi-separated and `U` is a quasi-compact
open of `X`, then the inclusion of the open `g ⁻¹ᵁ U` of `P` is quasi-compact. -/
lemma quasiCompact_preimage_ι {X P : Scheme.{u}} (g : P ⟶ X) [QuasiCompact g]
    [QuasiSeparatedSpace P] {U : X.Opens} (hU : IsCompact (U : Set X)) :
    QuasiCompact (g ⁻¹ᵁ U).ι :=
  have : CompactSpace (g ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp (g.isCompact_preimage hU)
  inferInstance

end AlgebraicGeometry
