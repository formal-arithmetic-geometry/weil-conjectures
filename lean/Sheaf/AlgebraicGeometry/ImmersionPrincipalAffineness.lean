/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Affineness of an immersion from a principal affine part

Source: Stacks Project, More on Groupoids in Spaces, Tag 0ABH (lemma-get-affine),
with the proof of Morphisms, Tag 0C3A (lemma-get-affine)
(blueprint: lem-sfb-immersion-principal-affineness).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact immersion into an affine scheme is affine as a scheme if the inverse
image of a principal open is affine and the image in its closed complement is closed.

Source: Stacks Project, More on Groupoids in Spaces, Tag 0ABH (lemma-get-affine)
(blueprint: lem-sfb-immersion-principal-affineness).

Proof, following Morphisms, Tag 0C3A with X = Spec A and U = D(f):
1. Factor j through a closed immersion into an open subscheme W of Spec A, using the
   immersion clause of def-weil-closed-immersion. Put C = j(V) intersect V(f).
2. At a point of W choose a basic open D(g) contained in W. It is affine by
   lem-weil-pbc-spec-localization-away-basic-open and
   lem-weil-pbc-principal-localization-open-immersion. Its inverse image is affine because
   closed immersions are affine (lem-weil-pbc-closed-immersion-integral-separated-uc and
   pqf-def-affine-morphism).
3. The source and target of j restricted over D(f) are affine. That restriction is affine
   by lem-weil-pbc-morphism-affine-schemes-affine, giving the required neighbourhood for
   each point of D(f).
4. For x outside W and D(f), choose a basic neighbourhood D(g) disjoint from the closed
   subset C. Then the inverse images of D(g) and D(g) intersect D(f) agree. The latter
   intersection is D(fg), an affine open of D(f) by the localization lemmas of step 2.
   The affine restriction in step 3 therefore has affine inverse image there
   (pqf-def-affine-morphism).
5. These neighbourhoods cover Spec A. By pqf-lem-affine-local-target, j is affine;
   applying pqf-def-affine-morphism to the affine target itself makes V affine.
-/
theorem isAffine_of_isImmersion_of_isAffineOpen_preimage_basicOpen_of_isClosed
    (A : Type u) [CommRing A] (V : Scheme.{u})
    (j : V ⟶ Spec (CommRingCat.of A)) [QuasiCompact j] [IsImmersion j] (f : A)
    (hprincipal : IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen f))
    (hclosed : IsClosed (Set.range j ∩ PrimeSpectrum.zeroLocus {f})) :
    IsAffine V := by
  sorry

end AlgebraicGeometry
