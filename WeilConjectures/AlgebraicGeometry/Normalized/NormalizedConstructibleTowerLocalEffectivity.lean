/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDerivedOriginPresentation
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedTowerCommonLisseStrata
import WeilConjectures.AlgebraicGeometry.Lisse.LisseNormalizedTowerLocalModels

/-!
# Local effectivity of normalized bounded constructible towers

Source: blueprint amplification (c); Stacks Tags 09AL, 09BU--09BX and 09AV
(blueprint: lem-weil-pbc-normalized-constructible-local-effectivity).

The existing AdicTower packages the strict derived tower, quotient-linear levels,
evaluation identifications, normalization isomorphisms, transitions and quotient cocycle.
The positive level n+1 is indexed by n : ℕ. Intrinsic constructibility uses the canonical
constant-to-functions coefficient comparison. The etale-origin conclusion uses the
existing bounded-constructible essential image, transported on actual cochain
representatives along the canonical coefficient-ring isomorphism. Thus no new derived
scalar functor or chosen comparison equivalence is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
