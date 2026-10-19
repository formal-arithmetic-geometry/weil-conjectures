/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTraceDiscriminantGluing
import Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantFibreEtaleCriterion

/-!
# The locally principal branch locus of a finite flat morphism

Source: Stacks Project, Tag 0BVH.
(blueprint: lem-sbc-finite-flat-discriminant-branch-support)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The discriminant ideal cuts out exactly the image of the non-etale locus.

Source: Stacks Project, Tag 0BVH (discriminant-lemma-discriminant),
as used in Tag 0BJH (pione-lemma-ramification-quasi-finite-flat).
(blueprint: lem-sbc-finite-flat-discriminant-branch-support)

Proof: Finite flat over a locally Noetherian target is finite locally free.
On a trivializing affine open write B as a free A-module and take the determinant
of the trace pairing B times B to A. Changing the basis multiplies this determinant
by the square of a unit, so the principal ideals glue to a quasi-coherent ideal J.
Thus J is locally principal. After tensoring with the residue field at y, the trace
pairing is nondegenerate exactly when the finite fibre algebra is etale. This is
exactly when the morphism is etale at every point of that fibre, by the finite flat
fibre criterion. The etale locus is open. Consequently the determinant vanishes
at y exactly when some point above y has no etale open neighbourhood. Rank zero
pieces have determinant one and empty branch locus; an identically zero determinant
is allowed and its support is the entire corresponding component. -/
theorem exists_locallyPrincipal_branch_ideal_of_finite_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] :
    ∃ J : Y.IdealSheafData, J.IsLocallyPrincipal ∧
      ∀ y : Y, y ∈ J.support ↔
        ∃ x : X, f x = y ∧ ¬ (∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) := by
  obtain ⟨J, hJ⟩ := exists_ideal_locally_eq_trace_discriminant_of_finite_flat f
  refine ⟨J, ?_, ?_⟩
  · intro y
    obtain ⟨U, hy, n, b, hb⟩ := hJ y
    refine ⟨U, hy, ?_⟩
    rw [hb]
    exact ⟨_, rfl⟩
  · intro y
    obtain ⟨U, hy, n, b, hb⟩ := hJ y
    rw [IdealSheafData.mem_support_iff_of_mem hy, hb, Y.zeroLocus_span]
    exact trace_discriminant_zeroLocus_iff_nonEtale_fibre f U y hy n b

end AlgebraicGeometry.Scheme
