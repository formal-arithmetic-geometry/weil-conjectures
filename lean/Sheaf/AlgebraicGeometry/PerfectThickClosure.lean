/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Perfect complexes form a thick subcategory

Source: literature/stacks-project/cohomology.tex, Tags 08CR (lemma-two-out-of-three-perfect)
and 08CS (lemma-summands-perfect), and Definition 08CM (blueprint: lem-pc-perfect-thick-closure).
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- Perfect complexes are closed under distinguished triangles, direct summands, shifts, and
finite direct sums.
Source: Stacks Project, Cohomology of Sheaves, Tags 08CR and 08CS and Definition 08CM
(blueprint: lem-pc-perfect-thick-closure).

Proof: Apply `lem-pc-perfect-two-out-of-three` (Tag 08CR) to each pair of perfect terms
of a distinguished triangle. Apply `lem-pc-perfect-summand` (Tag 08CS) to the decomposition
of a perfect binary direct sum to obtain perfectness of both summands. For shifts and finite
sums, use the local strictly perfect representatives of `def-pc-perfect-complex` (08CM).
For finitely many objects refine their open covers to common intersections. Shifting a
strictly perfect complex reindexes its finitely many nonzero terms. The termwise finite sum
of strictly perfect complexes is bounded and each term is a direct summand of a finite free
module. These local representatives give perfectness of the shifted and finite-sum objects.
-/
theorem perfect_thick_closure (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    (∀ (T : Triangle (schemeDerivedCategory X)),
      T ∈ distTriang (schemeDerivedCategory X) →
      (IsPerfect X T.obj₁ → IsPerfect X T.obj₂ → IsPerfect X T.obj₃) ∧
      (IsPerfect X T.obj₂ → IsPerfect X T.obj₃ → IsPerfect X T.obj₁) ∧
      (IsPerfect X T.obj₁ → IsPerfect X T.obj₃ → IsPerfect X T.obj₂)) ∧
    (∀ (K L : schemeDerivedCategory X),
      IsPerfect X (K ⊞ L) → IsPerfect X K ∧ IsPerfect X L) ∧
    (∀ (K : schemeDerivedCategory X) (n : ℤ),
      IsPerfect X K → IsPerfect X (K⟦n⟧)) ∧
    (∀ (I : Type v) [Finite I] (K : I → schemeDerivedCategory X),
      (∀ i : I, IsPerfect X (K i)) → IsPerfect X (⨁ K)) := by
  sorry

end AlgebraicGeometry.Scheme
