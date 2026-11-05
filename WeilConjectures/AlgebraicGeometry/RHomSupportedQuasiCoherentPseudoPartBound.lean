/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution

/-! # Lower bound for internal Hom out of a pseudo-coherent complex

The local lower-bound clause of the pseudo-coherent internal-Hom lemma: for `K`
pseudo-coherent and `L` bounded below, every point has an open neighbourhood on which the
cohomology sheaves of `RHom(K, L)` vanish below some degree (Stacks Project, Tag 0A6H,
clause (1)). -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
