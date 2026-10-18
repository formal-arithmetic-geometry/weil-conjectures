/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Irreducible

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.WellFounded

/-!
# Constructibility criterion on irreducible closed subsets of a Noetherian scheme

Source: literature/stacks-project/topology.tex, Tag 053Z (blueprint:
lem-trf-noetherian-constructible-subset-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open Topology TopologicalSpace

namespace AlgebraicGeometry

/-- A subset of a scheme covered by finitely many affine spectra of Noetherian rings is
constructible when it is generically either full or empty on every irreducible closed subset.

Source: literature/stacks-project/topology.tex, Tag 053Z, implication (2) to (1), with
Properties Tag 01OZ (blueprint: lem-trf-noetherian-constructible-subset-criterion).
Proof:
1. The given affine chart rings are the rings of sections by `def-weil-affine-spectrum`.
   The cover makes Y locally Noetherian (`pqf-def-locnoeth`). Each chart is quasi-compact
   (`lem-weil-pbc-affine-scheme-qcqs`); its finite subcover of any restricted cover, combined
   over the finitely many charts, makes Y quasi-compact (`def-weil-pbc-quasi-compact-scheme`).
   The minimal-closed-subset condition of
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` makes the underlying space Noetherian.
2. If E is not constructible, choose a minimal closed C for which E intersect C is not
   constructible in Y, using that same minimal-closed-subset lemma. Every proper closed
   subset D of C has constructible E intersect D. The empty set is constructible by
   `def-weil-constructible-subset`, so C is nonempty.
3. If C is reducible, `def-weil-irreducible-components` gives a binary decomposition into
   proper closed subsets C1 and C2. Their intersections with E are constructible by minimality.
   Finite-union closure (`def-weil-constructible-subset`) makes E intersect C constructible,
   a contradiction. Thus C is irreducible.
4. Apply hE to C and write its nonempty relatively open V as C intersect O for O open in Y.
   Then D = C minus V is closed and proper, so E intersect D is constructible. V is locally
   closed (`def-weil-locally-closed-subset`), hence constructible in the Noetherian ambient
   space by `def-weil-constructible-subset` (Tag 005L).
5. If V is contained in E, then E intersect C is the union of V and E intersect D, hence
   constructible. If V is disjoint from E, then E intersect C equals E intersect D, hence
   constructible. Both cases contradict the choice of C; taking C = Y gives the conclusion.
-/
theorem constructible_of_noetherian_affine_cover
    {Y : Scheme.{u}} (E : Set Y) (n : ℕ) (U : Fin n → Y.affineOpens)
    (hU : (⨆ i, (U i : Y.Opens)) = ⊤)
    (hN : ∀ i, IsNoetherianRing Γ(Y, U i))
    (hE : ∀ (Z : Set Y), IsClosed Z → IsIrreducible Z →
      ∃ (V : Set Y), V.Nonempty ∧ V ⊆ Z ∧
        (∃ O : Set Y, IsOpen O ∧ V = Z ∩ O) ∧
        (V ⊆ E ∨ V ∩ E = ∅)) :
    Topology.IsConstructible E := by
  sorry

end AlgebraicGeometry
