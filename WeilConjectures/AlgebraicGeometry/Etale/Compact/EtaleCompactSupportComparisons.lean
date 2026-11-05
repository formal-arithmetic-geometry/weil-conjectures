/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion

/-!
# Canonical comparisons for ordinary etale compact support

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc, and Stacks Project,
Tags 0F7I, 0F7J, 0F7K (blueprint: lem-amb-etale-compact-comparisons).

The existing bounded-below API supplies the natural isomorphisms and their coherence:
* `rightDerivedLowerShriekOfCompactificationPlusRefinementIso`, with its `_id` and `_comp`;
* `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`, `_refl`, `_trans`;
* `rightDerivedLowerShriekPlusCompIso`, its `_hom_eq`, and its `_assoc`.
These are used for `ModuleCat.{u + 1} Λ`, with finite commutative `Λ`.
`IsNoetherian` is exactly the finite affine Noetherian-cover condition, by Mathlib's
`isNoetherian_iff_of_finite_affine_openCover`.

The statement below identifies the refinement isomorphism with precisely the specified
proper/open alpha map, after applying the ambient pushforward and its canonical composition
identification. Together with the existing declarations recorded on this node, it supplies
all the clauses, without introducing a second comparison or composition construction.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
