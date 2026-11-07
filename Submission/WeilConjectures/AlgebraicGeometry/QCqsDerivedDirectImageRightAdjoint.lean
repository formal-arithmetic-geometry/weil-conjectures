/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Basic
import Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import Submission.WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import Submission.WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Submission.WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration
import Submission.WeilConjectures.CategoryTheory.BrownRepresentabilityHomLocallySmall
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Right adjoint to derived direct image on quasi-coherent complexes

Source: Stacks Project, Duality for Schemes, Lemma 48.3.1 (Tag 0A9E)
(blueprint: lem-pc-qcqs-derived-direct-image-right-adjoint).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
