/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sets.OpenCover

/-! # Cofinal finite affine open coverings of a qcqs scheme

Source: Stacks Project, Schemes, Tags 01IT and 01KO, and Algebra, Tag 00E8
(blueprint: lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Every open covering of a quasi-compact quasi-separated scheme has a finite affine open
refinement with quasi-compact pairwise intersections. Thus these finite coverings are cofinal
under refinement, as required in Stacks, Modules, Tag 01BS (3), and Sheaves, Tag 009F (4).

Source: Stacks Project, Schemes, Tags 01IT and 01KO, and Algebra, Tag 00E8
(blueprint: lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings).

Proof:
1. For each point `x` of `X`, choose a member `V a` of the given covering containing `x`.
   The affine basis theorem (Stacks 01IT, `Scheme.isBasis_affineOpens`) gives an affine open
   neighbourhood of `x` contained in `V a`. These neighbourhoods cover `X`. Quasi-compactness
   gives a finite subcover (`IsCompact.elim_finite_subcover`). Index it by a finite type `J` and
   retain the chosen indices in `A` to obtain the refinement map. This uses `def-pc-scheme`
   and `def-weil-pbc-scheme-conventions`.
2. Each selected affine open is quasi-compact (Stacks 00E8, `IsAffineOpen.isCompact`).
   Quasi-separatedness implies their pairwise intersections are quasi-compact
   (`pqf-lem-qs-intersection-qc`, or directly Stacks 01KO (1) implies (2)). Hence every
   covering is refined by a covering of the asserted class, which is precisely cofinality
   under refinement and the stated hypotheses of 01BS and 009F.
-/
theorem qcqs_scheme_cofinal_finite_affine_open_coverings
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type v} (V : A → X.Opens) (hV : TopologicalSpace.IsOpenCover V) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens) (a : J → A),
      TopologicalSpace.IsOpenCover U ∧
      (∀ j, IsAffineOpen (U j)) ∧
      (∀ j, U j ≤ V (a j)) ∧
      (∀ j j', IsCompact ((U j : Set X) ∩ (U j' : Set X))) := by
  sorry

end AlgebraicGeometry
