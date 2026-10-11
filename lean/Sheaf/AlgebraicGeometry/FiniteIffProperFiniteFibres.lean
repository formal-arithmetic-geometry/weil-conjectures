/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Finite morphisms and proper morphisms with finite fibres

Source: Stacks Project, Cohomology of Schemes, Lemma 30.21.1, Tag 02OG
(blueprint: thm-pqf-finite-iff-proper-finite-fibres).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over a locally Noetherian target, a morphism is finite if and only if it is proper
with finite fibres (Stacks Tag 02OG)
(blueprint: thm-pqf-finite-iff-proper-finite-fibres).

Proof outline from the DAG:
1. A finite morphism is proper (`lem-weil-pbc-finite-proper`) and quasi-finite
   (`pqf-lem-finite-qf`), hence has finite fibres (`pqf-lem-qf-finitefibres`).
2. Conversely, properness supplies finite type, local finite type and quasi-compactness
   (`pqf-lem-proper-basic`). Finite fibres then imply quasi-finiteness
   (`pqf-lem-qf-finitefibres`), which implies local quasi-finiteness
   (`pqf-lem-qf-locqf-qc`). Properness and local quasi-finiteness imply finiteness
   (`pqf-lem-proper-lqf-finite`). The locally Noetherian hypothesis is retained as in
   the source statement, although this route proves the reverse implication without it. -/
theorem isFinite_iff_isProper_and_hasFiniteFibres {X S : Scheme.{u}}
    [IsLocallyNoetherian S] (f : X ⟶ S) :
    IsFinite f ↔ IsProper f ∧ Scheme.Hom.HasFiniteFibres f := by
  sorry

end AlgebraicGeometry
