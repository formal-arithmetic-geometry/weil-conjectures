/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.GlobalGenerationNonvanishingCover

/-!
# Finite nonvanishing covers from global generation

Source: Stacks Project, Varieties, Lemma 09NC, proof, the second quasi-compactness step
(blueprint: lem-sc-finite-sections-cover-qc).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A globally generated invertible module on a quasi-compact scheme has finitely many
sections whose nonvanishing loci `nonvanishingLocus L (t j)` cover the scheme.

Source: Stacks Project, Varieties, Lemma 09NC, proof, second quasi-compactness step
(blueprint: lem-sc-finite-sections-cover-qc).

By `lem-sc-global-generation-nonvanishing-cover`, the nonvanishing loci of all global
sections cover `X`. Each locus is open, as recorded in
`def-weil-pbc-ample-invertible-module` (the tensor-power-one case). Quasi-compactness,
`def-weil-pbc-quasi-compact-scheme`, gives a finite subcover. Enumerating its sections as
`t : Fin m → Γ(X, L)` gives the asserted covering. -/
theorem finite_sections_cover_of_globally_generated (X : Scheme.{u}) [CompactSpace X]
    (L : X.Modules) [L.IsInvertible]
    (hgen : Nonempty (SheafOfModules.GeneratingSections L)) :
    ∃ (m : ℕ) (t : Fin m → L.val.presheaf.obj (Opposite.op ⊤)),
      ⋃ j, nonvanishingLocus L (t j) = Set.univ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
