/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Sheaf.AlgebraicGeometry.Dimension

/-!
# Effective Cartier divisors on proper schemes of dimension at most one

Source: Stacks Project, Tag 0AYY (varieties-lemma-degree-effective-Cartier-divisor)
(blueprint: lem-pc-cartier-divisor-finite-over-field)
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- An effective Cartier divisor on a proper scheme of dimension at most one is finite over
the field.  The divisor is represented by an invertible ideal sheaf `J` and its canonical closed
subscheme `J.subscheme`.

Source: Stacks Project, Tag 0AYY (varieties-lemma-degree-effective-Cartier-divisor), first two
sentences of the proof.  The dimension and closed-point clauses are the nowhere-dense dimension
drop; properness is inherited by the closed immersion; finiteness and affineness are the
zero-dimensional proper-scheme theorem (Tag 06LH).
(blueprint: lem-pc-cartier-divisor-finite-over-field)
-/
theorem effectiveCartierDivisor_finite_over_field
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hX : X.dim ≤ 1)
    (J : X.IdealSheafData) (hJ : J.IsInvertible) :
    J.subscheme.dim ≤ 0 ∧
      (∀ x : J.subscheme, IsClosed ({x} : Set J.subscheme)) ∧
      (¬ ∃ U : X.Opens, U ≠ ⊥ ∧ ∀ x : U, ∃ y : J.subscheme,
        J.subschemeι y = U.ι x) ∧
      IsAffine J.subscheme ∧
      IsFinite (J.subschemeι ≫ X ↘ Spec (.of k)) ∧
      (letI := (J.subschemeι ≫ X ↘ Spec (.of k)).ΓAlgebra
       FiniteDimensional k (Γ(J.subscheme, ⊤))) := by
  sorry

end AlgebraicGeometry
