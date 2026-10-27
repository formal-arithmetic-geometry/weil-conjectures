/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # The upper unitriangular group scheme

Source: Milne, Algebraic Groups (2017), Theorem 14.5(b)--(c), printed p.281,
including equation (92) (blueprint: def-sfb-unitriangular-group-scheme).

The coordinate algebra is the polynomial algebra in the strictly upper entries.
The three group maps have explicit coordinate formulas. Only their group axioms
are postponed; the unique-existence statement fixes all group structure data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.UnitriangularGroup

/-- Strictly upper matrix positions, with the same lifted indices as the existing GL scheme.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
abbrev Position (n : ℕ) :=
  {p : LinearGroupSchemes.Index.{u} n × LinearGroupSchemes.Index.{u} n //
    p.1.down < p.2.down}

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual polynomial coordinate algebra in all strictly upper entries.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
abbrev CoordinateRing := MvPolynomial (Position.{u} n) k

/-- The universal upper triangular matrix with diagonal entries one.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def matrix :
    Matrix (LinearGroupSchemes.Index.{u} n) (LinearGroupSchemes.Index.{u} n)
      (CoordinateRing k n) :=
  fun i j ↦ if i = j then 1 else
    if h : i.down < j.down then MvPolynomial.X ⟨(i, j), h⟩ else 0

/-- The coordinate map for matrix multiplication, equivalently formula (92).
Source: Milne, Theorem 14.5(b)--(c), equation (92), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def comul : CoordinateRing k n →ₐ[k]
    CoordinateRing k n ⊗[k] CoordinateRing k n :=
  MvPolynomial.aeval (fun p : Position.{u} n ↦
    ∑ r, matrix k n p.val.1 r ⊗ₜ[k] matrix k n r p.val.2)

/-- Evaluation at the identity matrix, sending every strictly upper coordinate to zero.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def counit : CoordinateRing k n →ₐ[k] k :=
  MvPolynomial.aeval (fun _ ↦ 0)

/-- Inversion by the finite geometric series for I+N, since N is strictly upper triangular.
Source: Milne, Theorem 14.5(b)--(c), p.281, the group U_n
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def antipode : CoordinateRing k n →ₐ[k] CoordinateRing k n :=
  MvPolynomial.aeval (fun p : Position.{u} n ↦
    (∑ r ∈ Finset.range n, (1 - matrix k n) ^ r) p.val.1 p.val.2)

/-- The affine k-scheme Spec k[x_ij : i<j], with its canonical structure morphism.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def scheme : Over (Spec (.of k)) :=
  (algSpec (.of k)).obj (op (CommAlgCat.of k (CoordinateRing k n)))

/-- The multiplication morphism induced by the displayed polynomial comultiplication.
Source: Milne, Theorem 14.5(b)--(c), equation (92), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def multiplication : scheme k n ⊗ scheme k n ⟶ scheme k n :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.μ (algSpec (.of k))
      (op (CommAlgCat.of k (CoordinateRing k n)))
      (op (CommAlgCat.of k (CoordinateRing k n))) ≫
    (algSpec (.of k)).map (CommAlgCat.ofHom (comul k n)).op

/-- The identity section, induced by evaluation of the strictly upper entries at zero.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def identitySection : 𝟙_ (Over (Spec (.of k))) ⟶ scheme k n :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.ε (algSpec (.of k)) ≫
    (algSpec (.of k)).map (CommAlgCat.ofHom (counit k n)).op

/-- The inverse morphism, induced by the explicitly given finite geometric series.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable def inverse : scheme k n ⟶ scheme k n :=
  (algSpec (.of k)).map (CommAlgCat.ofHom (antipode k n)).op

/-- These three explicit maps uniquely determine a group scheme structure.
Source: Milne, Theorem 14.5(b)--(c), equation (92), p.281
(blueprint: def-sfb-unitriangular-group-scheme).

Proof: algebra maps from the polynomial ring are uniquely determined by the upper entries.
Their evaluations identify algebra-valued points with upper unitriangular matrices.
The comultiplication evaluates to matrix multiplication, and the counit to the identity.
For a strictly upper n by n matrix N, N^n=0: a nonzero summand of an entry of N^n
would require n+1 strictly increasing indices among n indices. Thus the finite series
sum_{r=0}^{n-1}(-N)^r is both a left and a right inverse of I+N. Associativity and the
unit laws follow from matrix multiplication, and equality on universal polynomial entries
proves the scheme diagrams. All three data fields of GrpObj are fixed, so proof
irrelevance gives uniqueness. For n=0 the coordinate index is empty and Spec k is trivial. -/
theorem group_existsUnique :
    ∃! h : GrpObj (scheme k n),
      h.one = identitySection k n ∧ h.mul = multiplication k n ∧ h.inv = inverse k n := by
  sorry

/-- The group structure with precisely the three specified coordinate maps.
Source: Milne, Theorem 14.5(b)--(c), p.281
(blueprint: def-sfb-unitriangular-group-scheme). -/
noncomputable instance group : GrpObj (scheme k n) :=
  (group_existsUnique k n).exists.choose

end AlgebraicGeometry.UnitriangularGroup
