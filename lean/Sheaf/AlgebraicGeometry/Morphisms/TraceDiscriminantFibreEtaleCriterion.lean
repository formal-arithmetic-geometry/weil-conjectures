/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Discriminant

import Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantEvaluationEtaleFibre
import Sheaf.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods

/-!
# Local trace discriminants detect non-etale fibres

Source: Stacks Project, Tag 0BVH, Lemma 49.3.1.
(blueprint: lem-sbc-trace-discriminant-fibre-etale-criterion)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- On a free affine chart, the trace determinant vanishes precisely over a non-etale point.

Source: Stacks Project, Tag 0BVH, Lemma 49.3.1, and its finite flat fibre criterion.
(blueprint: lem-sbc-trace-discriminant-fibre-etale-criterion)

Proof: The preimage of the affine target chart is affine because f is finite. The chosen
basis makes its section algebra finite free. Tensor its multiplication matrices with the
residue field at y; taking traces and determinants commutes with this operation. Thus the
trace determinant vanishes at y exactly when the trace pairing of the finite fibre algebra
is degenerate. Over a field a finite algebra has nondegenerate trace pairing precisely
when it is a product of finite separable field extensions: nilpotents are in the radical
of the trace form; after reduction the algebra is a product of fields, and the trace form
on each field is nondegenerate precisely for a separable extension. Hence nonvanishing is
equivalent to an etale fibre. For a flat morphism of finite presentation the fibre is
etale precisely when f is etale at each of its points. The etale locus is open, so this
means each x above y has a source open neighbourhood V with etale V.ι followed by f.
Negating this universal statement gives the existential on the right. In rank zero the
fibre is empty and the determinant is one, so both sides are false. A zero determinant
is permitted, and makes both sides true at every point of the chart. -/
theorem trace_discriminant_zeroLocus_iff_nonEtale_fibre
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
      y ∈ Y.zeroLocus {Algebra.discr Γ(Y, U.1) b} ↔
        ∃ x : X, f x = y ∧ ¬ (∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) := by
  classical
  let := (f.app U.1).hom.toAlgebra
  dsimp only
  intro n b
  have heval := trace_discriminant_evaluation_ne_zero_iff_etale_fibre f U y hy n b
  have hzero : y ∈ Y.zeroLocus {Algebra.discr Γ(Y, U.1) b} ↔
      Y.evaluation U.1 y hy (Algebra.discr Γ(Y, U.1) b) = 0 := by
    rw [Y.zeroLocus_singleton]
    exact (Y.evaluation_eq_zero_iff_notMem_basicOpen y hy _).symm
  rw [hzero]
  constructor
  · intro hz
    by_contra h
    push Not at h
    have hE := (etale_fibre_iff_forall_etale_neighbourhood f y).mpr h
    exact (heval.mpr hE) hz
  · rintro ⟨x, hxy, hx⟩
    by_contra hz
    have hE := heval.mp hz
    exact hx ((etale_fibre_iff_forall_etale_neighbourhood f y).mp hE x hxy)

end AlgebraicGeometry.Scheme
