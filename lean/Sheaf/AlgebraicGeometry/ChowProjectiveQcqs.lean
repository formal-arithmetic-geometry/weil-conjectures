/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q11
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ChowFiniteType

/-!
# Chow's lemma over a qcqs base with a finite homogeneous coordinate set

Source: Stacks Project, Lemma 32.12.1, Tag 0202 (`limits.tex`, `lemma-chow-finite-type`);
Weil conjectures blueprint, `sec-nagata-compactification`, unit `sk-thm-chow-projective`,
node `det-chow-projective-qcqs-chow` (blueprint: det-chow-projective-qcqs-chow).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Chow's lemma for a separated finite-type morphism over a quasi-compact quasi-separated
scheme, with projective space indexed by a finite set of homogeneous coordinates.

Source: Stacks Project, Lemma 32.12.1, Tag 0202; current blueprint, unit
`sk-thm-chow-projective` (blueprint: det-chow-projective-qcqs-chow).

Proof: apply `exists_chow_finite_type` (node `lem-weil-pbc-chow-finite-type`) to `f`.
Its assumptions are precisely the qcqs hypotheses on `S` and separatedness and finite type
of `f`. It supplies `n : ℕ`, `X'`, a proper surjective `π`, an immersion `j` into
`ProjectiveSpace (ULift.{u} (Fin (n + 1))) S`, and the equality over `S`. Set
`N = ULift.{u} (Fin (n + 1))`, which is finite, and take the same `X'`, `π`, and `i = j`.
By `def-nagata-projective-space-base-change`, this is exactly the projective space with
homogeneous coordinates indexed by `N`, and its structure morphism is the first projection.
Thus the three morphism properties and the equality give every conclusion unchanged.
The cited Chow theorem carries the blueprint's paragraph-3 route: finite-presentation
envelope (01ZJ), Noetherian approximation (01ZA), separated descent (01ZM/01ZQ),
Noetherian Chow (0200), base change back to `S`, and pullback to `X`. -/
theorem exists_chow_projective_qcqs {S X : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (N : Type u) (_ : Finite N) (X' : Scheme.{u}) (π : X' ⟶ X)
      (i : X' ⟶ ProjectiveSpace N S),
      IsProper π ∧ Surjective π ∧ IsImmersion i ∧
        i ≫ ProjectiveSpace N S ↘ S = π ≫ f := by
  sorry

end AlgebraicGeometry
