/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Connectivity of the derived tensor product

Source: `literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-sf-kunneth-ordinary/lem-kun-derived-tensor-t-est.md`, node
`lem-kun-derived-tensor-t-est`; Stacks Project, Tag 0F1J, first reduction paragraph,
using Tag 0F1M and the lower truncation of Tag 0118.

The first factor has Tor amplitude in `[a, ∞)`, and the second factor has no
cohomology below `b`. We use bounded dévissage for each canonical upper truncation
of the second factor. An unrestricted categorical K-flat model of the first factor
computes every tensor product. The upper truncations have colimit the original
complex, tensoring preserves this colimit, and exact filtered colimits preserve
exactness at each degree below `a + b`. Thus no comparison between the independent
coefficient K-flat predicate and categorical K-flatness is needed.

The finite dévissage is the existing `DerivedCategory.isGE_obj_of_isGE` from
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
The exact-colimit step is proved below from Mathlib's `colim.exact_mapShortComplex`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
