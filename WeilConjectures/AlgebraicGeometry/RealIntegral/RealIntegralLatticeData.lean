/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteModuleLift
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisFiniteTensorScalarBraided
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# A complete integral lattice for one finite coefficient extension

Source: the current blueprint `sec-lattices/sk-p-real-integral`, finite reductions,
completed fibre, and independence of lattice paragraphs.
(blueprint: def-real-integral-complete-lattice)

The imported geometric-fibre constructions are registered separately by
`def-real-integral-fibre-interfaces`. No correspondence theorem is used here.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.LisseQlbar
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RealIntegral

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
  (X : Scheme.{u})

local instance fieldMon : MonObj (condensedRingObj (fieldRing l E) X) :=
  Functor.monObjObj (F := upperStarFromPoint X) (fieldRing l E)

local instance integerMon : MonObj (condensedRingObj (integerRing l E) X) :=
  Functor.monObjObj (F := upperStarFromPoint X) (integerRing l E)

/-- The quotient coefficient ring in the sheaf-value universe. The index `n` means
reduction modulo the positive power `π^(n+1)`; omitting the zero quotient is cofinal.
Source: blueprint `sk-p-real-integral`, finite-reduction paragraph.
(blueprint: def-real-integral-complete-lattice) -/
abbrev Residue (n : ℕ) := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

local instance residueFinite (n : ℕ) : Finite (Residue.{u} l E n) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  infer_instance

set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Elaborating the canonical coefficient and fibre comparisons unfolds large sheaf types.
end AlgebraicGeometry.ProEtale.RealIntegral
