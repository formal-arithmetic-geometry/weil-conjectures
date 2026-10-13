/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Separable

/-!
# Separable residue extensions of standard tame root charts

Source: Stacks Project, Tag 0EYH, displayed local normal form.
(blueprint: lem-sbc-tame-root-product-residue-separable)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Finite products of standard root charts have separable residue extensions.

Source: Stacks Project, Tag 0EYH, displayed local normal form.
Proof: A point of the spectrum of the finite product selects exactly one factor;
the empty product has no points. Write k for the residue field of its base point
and t for the image of the root coordinate. The fibre of that factor is
k[T]/(T^e-fbar). If fbar is zero, positivity of e gives t=0 in the residue field,
so the residue field is k. Otherwise t is nonzero. The derivative e*T^(e-1) is
nonzero at t because e is invertible. Hence the irreducible polynomial defining
this point is separable. Its quotient field is the residue field of the point.
These identifications use the canonical structure maps, so the same conclusion
holds for the canonical map on scheme residue fields. No regularity of R or
nonzerodivisor assumption on f is required; e=1 and f=0 are included.
(blueprint: lem-sbc-tame-root-product-residue-separable) -/
theorem tameRootProduct_residue_separable (R : CommRingCat.{u})
    (m : ℕ) (f : R) (e : Fin m → ℕ)
    (he : ∀ k, 0 < e k ∧ IsUnit (e k : R)) :
    let D := CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))
    let π : Spec D ⟶ Spec R :=
      Spec.map (CommRingCat.ofHom (algebraMap R D))
    ∀ x : Spec D,
      letI := (π.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable ((Spec R).residueField (π x)) ((Spec D).residueField x) := by
  sorry

end AlgebraicGeometry.Scheme
