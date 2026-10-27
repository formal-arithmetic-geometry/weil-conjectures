/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.Topology.Spectral.Basic
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Compactness.Compact
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # The point space of a qcqs algebraic space is spectral

Source: Stacks Project, Properties of Spaces, Tag 0A4G, with the absolute
quasi-separatedness criterion of Tag 0AHR (blueprint: lem-sfb-qcqs-space-spectral).

The topology is the existing atlas topology on field-valued point classes. The base
scheme is arbitrary; absolute quasi-separatedness imposes no condition on that base.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact, absolutely quasi-separated algebraic space has spectral point space.
Source: Stacks Project, Properties of Spaces, Tag 0A4G; Tag 0AHR identifies the affine
fibre-product criterion with quasi-compactness of the absolute diagonal
(blueprint: lem-sfb-qcqs-space-spectral).

Proof:
1. By lem-sfb-space-quasicompact-affine-tests, absolute diagonal quasi-compactness
   survives base change to the relative product over S. Its pullbacks impose equality
   of the same two maps to X. Thus lem-sfb-quasiseparated-space-sober applies, giving
   a unique generic point for every nonempty irreducible closed subset.
2. Choose an affine surjective etale scheme atlas U by lem-sfb-qc-space-affine-etale-atlas.
   Its quotient topology agrees with the topology here by lem-a1-space-affine-etale-cover.
   Restrict to affine opens V of U. Open immersions and compositions are etale by
   lem-weil-pbc-etale-composition-cancellation. The images of these V are open and their
   point maps continuous by lem-a1-space-point-open-calculus. They are quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-continuous-image-quasi-compact.
   For x in an open O, lift x to U and use lem-weil-pbc-affine-opens-basis inside the
   inverse image of O. The resulting chart images form a basis of quasi-compact opens.
3. Cover two quasi-compact opens A and B by finitely many such affine chart images.
   By lem-sfb-space-affine-source-qc-separated each affine chart V maps quasi-compactly
   to X, so V times_X W is quasi-compact for every other affine chart W. Compatible
   point lifting in lem-a1-space-point-open-calculus identifies its image with the
   intersection of the two chart images. Continuity and
   lem-weil-pbc-continuous-image-quasi-compact make that intersection quasi-compact.
   A intersect B is a finite union of these intersections: restrict an open cover to
   each piece and combine its finite subcovers. Empty covers and empty opens are allowed.
4. The assumed quasi-compactness, sobriety from step 1, basis from step 2, and intersection
   property from step 3 give exactly def-weil-spectral-space, namely SpectralSpace. -/
theorem spectralSpace_of_compact_of_absolutelyQuasiSeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X) :
    SpectralSpace (Point X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
