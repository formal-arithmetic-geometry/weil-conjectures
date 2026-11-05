/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc

/-! # Cohomology sheaves of internal Hom out of a pseudo-coherent complex

The degreewise calculation behind the quasi-coherence clause of the pseudo-coherent
internal-Hom lemma: locally, each cohomology sheaf of the Hom complex is computed by a
truncation of a bounded-above finite free model (Stacks Project, Tag 0A6H, clause (1)). -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
