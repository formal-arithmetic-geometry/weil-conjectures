/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.CategoryTheory.FilteredCohomologyImage

/-! # Compatibility name for the cohomology image filtration

The construction and its finiteness theorem are supplied by the adopted source library.
The original Sheaf name remains an abbreviation for consumers using that interface.
Source: Stacks Project, Tags 012P and 012W.
(blueprint: lem-sp-filtered-cohomology-image-finite).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (L : DecreasingFiltration K)

/-- The image of each filtered subcomplex in cohomology. The factorization of inclusions
and functoriality of homology prove antitonicity.
Source: Stacks Project, Tag 012P.
(blueprint: lem-sp-filtered-cohomology-image-finite). -/
noncomputable abbrev cohomologyImage (n : ℤ) : DecreasingFiltration (K.homology n) :=
  L.homologyFiltration n

end CategoryTheory.DecreasingFiltration
