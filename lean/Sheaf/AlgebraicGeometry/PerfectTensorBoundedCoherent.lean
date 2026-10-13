/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Bounded coherent cohomology of a perfect tensor

Source: Stacks Project, Tags 0DJQ and 01Y0
(blueprint: lem-pc-perfect-tensor-bounded-coherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Tensoring with a perfect object preserves bounded coherent cohomology on a
Noetherian scheme, without any relative flatness or proper-support hypothesis.
Source: Stacks Project, Tag 0DJQ, proof of Lemma 36.27.2 (local tensor calculation),
and Tag 01Y0 (closure of coherent sheaves under kernels and cokernels).

Proof:
1. Take a finite open cover of X with strictly perfect representatives P for E. Such a
   finite cover exists by compactness of X and the definition of IsPerfect. Write [c,d]
   for the bounds of G and [a_j,b_j] for those of each representative on the finite cover.
2. The terms of P are summands of finite free modules, hence flat. Thus the restriction
   of the derived tensor is represented by the ordinary total tensor complex P tensor G.
   Its degree n terms are summands of finite sums of coherent terms of G, hence coherent.
   Kernel and cokernel closure (01Y0) makes its cohomology coherent. Coherence is local,
   so the global cohomology sheaves are coherent.
3. The j-th total tensor vanishes outside [a_j+c,b_j+d]. Choose one interval containing
   these finitely many intervals. Vanishing of cohomology is local, giving global bounds.
   If X is empty, every sheaf is zero and any interval suffices.
(blueprint: lem-pc-perfect-tensor-bounded-coherent). -/
theorem perfect_tensor_bounded_coherent
    {X : Scheme.{u}} [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hGcoherent : ∀ n : ℤ, RingedSpace.IsCoherent X.toRingedSpace (G.X n)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
            (E ⊗ DerivedCategory.Q.obj G))) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
            (E ⊗ DerivedCategory.Q.obj G))) := by sorry

end AlgebraicGeometry.Scheme
