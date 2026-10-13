/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Discriminant

/-!
# Evaluating a trace discriminant on a fibre

Source: Stacks Project, Tag 0BJF, discriminant-lemma-discriminant, fibre-algebra argument.
(blueprint: lem-sbc-trace-discriminant-evaluation-etale-fibre)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The evaluated discriminant of a finite free affine section algebra is nonzero exactly
when the scheme-theoretic fibre is etale.

Source: Stacks Project, Tag 0BJF, discriminant-lemma-discriminant, fibre-algebra argument.
(blueprint: lem-sbc-trace-discriminant-evaluation-etale-fibre)

Proof: Put R = Gamma(Y,U), B = Gamma(X,f^{-1}U), and k = kappa(y), with R acting on k
by evaluation. Since f is affine, its fibre is Spec(k tensor_R B). The given basis of B
base changes to a k-basis of this algebra. In these bases the multiplication matrices
base change entrywise. Matrix trace and determinant commute with evaluation, so the
image of the discriminant is the determinant of the trace pairing on k tensor_R B.
A nondegenerate trace pairing forces every nilpotent to be zero: multiplication by a
nilpotent times any element is nilpotent, hence has zero trace, placing that nilpotent
in the radical of the pairing. A finite-dimensional reduced commutative k-algebra is
a finite product of fields. Its trace pairing is the orthogonal sum of the field trace
pairings, each nondegenerate exactly for a separable field extension. Thus the determinant
is nonzero exactly for a finite product of finite separable extensions, equivalently an
etale k-algebra and an etale fibre scheme. Conversely the same product decomposition
of an etale finite k-algebra gives nondegeneracy. If n=0, B and the fibre algebra are
the zero ring, the fibre is empty, and the determinant of the empty matrix is one.
No flatness or Noetherian hypothesis is needed. -/
theorem trace_discriminant_evaluation_ne_zero_iff_etale_fibre
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
      Y.evaluation U.1 y hy (Algebra.discr Γ(Y, U.1) b) ≠ 0 ↔
        Etale (f.fiberToSpecResidueField y) := by sorry

end AlgebraicGeometry.Scheme
