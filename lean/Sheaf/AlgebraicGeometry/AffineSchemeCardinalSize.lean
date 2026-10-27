/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCardinalSize
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Defs.Filter

/-! # The cardinal size of an affine scheme

Source: Stacks Project, sets.tex, Tag 000P, lemma-bound-affine; the size definition is in
section-categories-schemes preceding Tag 000I (blueprint: lem-sfb-affine-scheme-size).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- The cardinal size of an affine scheme is the maximum of the countable cardinal and
the cardinality of its ring of global sections. This includes the empty affine scheme
and the zero ring.

Source: Stacks Project, sets.tex, Tag 000P, lemma-bound-affine
(blueprint: lem-sfb-affine-scheme-size).

Proof plan:
1. Put A = Γ(Y, ⊤) and κ = max(ℵ₀, |A|). The top affine open identifies Y with Spec A by
[lem-weil-pbc-affine-open-spec-points]. Isomorphisms preserve affine opens and their section
rings, hence cardinal size. The top affine open in [def-sfb-scheme-cardinal-size] already
gives cardinalSize Y ≥ κ.
2. By [lem-weil-pbc-spec-localization-away-basic-open](i), every affine open U of Spec A is
covered by principal opens D(f) contained in U. By [lem-weil-pbc-affine-scheme-qcqs] and
[def-weil-pbc-quasi-compact-scheme], choose a finite subcover D(f₁), ..., D(fₙ). For the
empty open the empty list is allowed.
3. Finite lists of elements of A with affine principal-open union surject onto the affine
opens. By [lem-weil-pbc-finite-list-cardinality], their cardinality is at most κ.
4. By [def-weil-ring-localization-away], a tuple in the finite product of the A[fᵢ⁻¹] has
fractions with a common exponent m. Lists in A of length n + m map onto these tuples by
using their first n entries as numerators and m as exponent; trailing entries can be zero.
Thus [lem-weil-pbc-finite-list-cardinality] bounds the product by κ. This includes n = 0,
fᵢ = 0, nilpotents, and the zero ring, without injectivity of the localization maps.
5. By [lem-weil-pbc-affine-open-section-vanishing-prime](b), the sections on D(fᵢ) are A[fᵢ⁻¹].
The structure sheaf is a sheaf of rings by [def-weil-locally-ringed-space-morphism]. The
uniqueness axiom on the open cover, as in [def-sc-zariski-site], injects Γ(U, O) into this
finite product, so its cardinality is at most κ. On the empty open the empty-cover sheaf
axiom makes its section ring a singleton.
6. Both contributions to [def-sfb-scheme-cardinal-size] are at most κ, so cardinalSize Y ≤ κ.
Combine with step 1. For the zero ring the spectrum is empty, its only open has singleton
section ring, and both sides are ℵ₀. -/
theorem cardinalSize_of_isAffine (Y : Scheme.{u}) [IsAffine Y] :
    Y.cardinalSize = max Cardinal.aleph0 (Cardinal.mk ↥Γ(Y, ⊤)) := by
  sorry

end AlgebraicGeometry.Scheme
