/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AffineCurveRange.LatticePiece.CurveLatticeCompactData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-!
# Completion comparison for ordinary integral compact supports

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, lattice paragraph.
The object on the left is constructed by compactification, before any derived limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

namespace WeilConjectures.AffineCurveRange

/-- The geometric field of a finite-field datum is algebraically closed.
Source: the geometric base change in the range proof
(blueprint: lem-zl-curve-lattice-completion-comparison). -/
abbrev completionDatumIsAlgClosed (D : FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

attribute [local instance] completionDatumIsAlgClosed

/-- Ordinary integral compact support of a lisse lattice is the derived limit
of the compact supports of its canonical derived reductions, after forgetting
scalars. No finite-level cohomological bound is assumed in this comparison.

Source: latest blueprint, `lem-zl-affine-curve-range.proof.md`, lattice paragraph;
range node step 7 (blueprint: lem-zl-curve-lattice-completion-comparison).

Proof: the integral lisse lattice is constructible and has Tor amplitude [0,0].
Finite-Tor constructible stability puts its compact-support direct image in
bounded constructible integral modules on Spec k. The integral criterion implies
derived completeness. Its canonical completion cone expresses that actual
output as the derived limit of its reductions. Scalar comparison for compact
support identifies each output reduction with compact support of the input
reduction. Prove the transition squares using the scalar tower coherence and
the quotient maps defining AdicCompletion.derivedTower. These give an isomorphism
of whole towers, rather than unrelated isomorphisms at the levels. Derived
global sections commute with this derived limit; at the geometric point they
are the exact scalar sections. Exact restriction to underlying abelian groups
preserves products and the distinguished Roos triangle. Its image is precisely
the displayed derived-limit comparison. The empty piece and rank-zero lattice
give the zero tower and its zero triangle.
-/
theorem curveLattice_completionComparison (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (d : LatticePiece ell D.k) :
    IsDerivedLimit (C := DerivedCategory.{u + 1} Ab.{u + 1})
      (K := fun n : ℕ ↦ d.abelianTower.obj (Opposite.op n))
      (fun n ↦ d.abelianTower.map (homOfLE (Nat.le_succ n)).op) d.abelianComplex := by
  sorry

end WeilConjectures.AffineCurveRange
