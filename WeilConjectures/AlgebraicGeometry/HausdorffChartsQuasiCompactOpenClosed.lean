/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenIntersection

/-!
# Quasi-compact opens in schemes with Hausdorff affine charts

Source: Stacks Project, Properties, Tag 0CKV, `lemma-dimension-zero`, proof of
(1) implies (2), applying the local closedness argument to any quasi-compact open;
Topology, Tag 08YB (1).
(blueprint: lem-sfb-hausdorff-charts-qc-open-closed).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact open of a quasi-separated scheme covered by Hausdorff affine opens
is closed, and its original open inclusion is a closed immersion. In particular, the
closed immersion uses the given restricted structure sheaf. Neither the covering nor
`X` is assumed quasi-compact, and empty opens and schemes are allowed.

Source: Stacks Project, Properties, Tag 0CKV, `lemma-dimension-zero`, proof of
(1) implies (2), generalized from affine opens to quasi-compact opens;
Topology, Tag 08YB (1).
(blueprint: lem-sfb-hausdorff-charts-qc-open-closed).

Proof:
1. Each affine chart `V j` is quasi-compact by `lem-weil-pbc-affine-scheme-qcqs`.
   The node `pqf-lem-qs-intersection-qc`, namely
   `compactSpace_inter_of_quasiSeparated`, makes `U ⊓ V j` quasi-compact.
   Its topology is the subspace topology, also when regarded inside `V j`.
2. The node `lem-sfb-compact-subset-hausdorff-closed`, namely `IsCompact.isClosed`,
   shows that this intersection is closed in the Hausdorff chart `V j`.
3. The complement of `U` is the union over `j` of `V j` minus `U`. Each difference
   is open in `V j`, hence in `X`. The covering identity makes the union the whole
   complement, so `U` is closed. This uses an arbitrary union, including an empty one.
4. By `def-weil-open-immersion`, `U.ι` has the restricted structure sheaf and is a
   homeomorphism onto `U`, now closed. For each open `W` of `X`, glue any section
   on `W ∩ U` with zero on `W` minus `U`, a disjoint open cover of `W`. This proves
   surjectivity of the structure-sheaf map even on sections. Thus
   `def-weil-closed-immersion` applies to this same `U.ι`. For the empty open, only
   the zero section is needed. No Noetherian or global quasi-compactness assumption
   enters this argument. -/
theorem isClosed_and_isClosedImmersion_of_hausdorff_affine_cover
    (X : Scheme.{u}) [QuasiSeparated (terminal.from X)]
    (J : Type v) (V : J → X.Opens)
    (hVaffine : ∀ j : J, IsAffineOpen (V j))
    (hVhausdorff : ∀ j : J, T2Space (V j).toScheme)
    (hVcover : iSup V = ⊤) (U : X.Opens) [CompactSpace U.toScheme] :
    IsClosed (U : Set X) ∧ IsClosedImmersion U.ι := by
  sorry

end AlgebraicGeometry
