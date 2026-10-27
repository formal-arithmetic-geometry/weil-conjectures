/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.WellFounded

/-! # Noetherian topology of a quasi-compact locally Noetherian algebraic space

Source: Stacks Project, Properties of Spaces, Tag 04ZF, lemma-Noetherian-topology (2)
(blueprint: lem-sfb-noetherian-space-topology).

Quasi-compactness means the finite-subcover property of the atlas point topology.
Local Noetherianity is tested on every object of the small étale site.
The conclusion spells out the minimal-closed-subset characterization of Noetherianity.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every nonempty family of closed subsets of a quasi-compact, locally Noetherian
algebraic space has a member minimal under inclusion.
Source: Stacks Project, Tag 04ZF, lemma-Noetherian-topology (2), with Noetherianity in
its minimal-closed-subset form (blueprint: lem-sfb-noetherian-space-topology).

Proof:
1. By lem-a1-space-affine-etale-cover, the quotient topology of a surjective étale
   scheme atlas agrees with the final topology of def-a1-space-point-topology:
   all étale scheme-source maps are continuous and the atlas is one of these maps.
   Apply lem-sfb-qc-space-affine-etale-atlas to quasi-compactness to obtain an affine
   scheme W and a representable surjective étale map p from W to X. Its point map q
   is continuous and surjective by lem-a1-space-point-open-calculus (or the
   scheme-source clauses of lem-a1-space-affine-etale-cover).
2. The local Noetherianity hypothesis applied to the étale chart p makes W locally
   Noetherian. Affine quasi-compactness (lem-weil-pbc-affine-scheme-qcqs) makes W a
   Noetherian scheme. No quasi-separatedness of X is needed.
3. Given a nonempty family C of closed subsets of the point space, continuity of q
   makes the inverse images a nonempty family of closed subsets of W. By
   lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, choose a minimal inverse
   image and a member Z of C giving that inverse image.
4. If Z' in C were strictly contained in Z, choose a point in Z outside Z' and lift
   it through the surjective map q. Its lift witnesses strict containment of the
   inverse images, contradicting minimality. Thus Z is minimal in C. This also
   applies to the empty space, whose only closed subset is empty. -/
theorem exists_minimal_closed_of_quasiCompact_locallyNoetherian
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : CompactSpace (Point X.obj.obj))
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)) :
    ∀ C : Set (Set (Point X.obj.obj)), C.Nonempty →
      (∀ Z ∈ C, IsClosed Z) → ∃ Z ∈ C, ∀ Z' ∈ C, ¬ Z' ⊂ Z := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
