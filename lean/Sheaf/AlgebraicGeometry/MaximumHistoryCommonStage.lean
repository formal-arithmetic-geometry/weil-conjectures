/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.MaximumHistoryChronology

/-! # Regularity at common stages of maximum histories

Source: ILO VIII 2.1.1--2.1.4 and 2.3.4, 2.3.11, pp. 86--87, 91--93;
the common-prefix induction of (blueprint: lem-trf-maximum-history-common-stage).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open EmbeddedResolutionHistory

/-- Regularity is independent of the representatives chosen in a common finite prefix.
Source: ILO VIII 2.1.1--2.1.4, 2.3.4, 2.3.11, pp. 86--87, 91--93
(blueprint: lem-trf-maximum-history-common-stage).

Proof: induct on the common stage. At stage zero identify both diagrams with the
specified input pair using their normalized initial isomorphisms. Maintain ambient and
intrinsic isomorphisms on the entire common prefix, commuting with the inclusions and
preserving every earlier center ideal. This gives a smooth comparison over the identity
input pair without deletions. At a successor stage smoothValues identifies the current
value functions under this comparison. The greatest positive values and their full loci
therefore agree. Both centers are reduced by IsMaximumStep. On an affine open reduced
closed subschemes with the same support have the same radical ideal, so their intrinsic
ideals agree. Composing their closed embeddings with the intrinsic inclusion identifies
the ambient ideals as well. The center extended to each blowup is invertible by
principalization. The universal property of the ordinary blowup gives inverse comparison
maps; uniqueness of the lifts proves their composites are identities. Under this
ambient isomorphism the open complements and their scheme-theoretic closures agree,
so the strict transforms are isomorphic as well. This extends the prefix comparison and
its retained center equations. Isomorphic schemes have equivalent local Noetherianity
and isomorphic stalks, hence equivalent IsRegularScheme predicates. The argument stops
at the given common index; no terminal stage or lower-cut tower is assumed. -/
theorem maximumHistorySegment_commonStage {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}} {r s : ℕ}
    (T : MaximumHistorySegment ν A r) (U : MaximumHistorySegment ν A s)
    (i : ℕ) (hi : i ≤ r) (hj : i ≤ s) :
    IsRegularScheme (T.history ⟨i, Nat.lt_succ_of_le hi⟩).X ↔
      IsRegularScheme (U.history ⟨i, Nat.lt_succ_of_le hj⟩).X := by
  sorry

end AlgebraicGeometry
