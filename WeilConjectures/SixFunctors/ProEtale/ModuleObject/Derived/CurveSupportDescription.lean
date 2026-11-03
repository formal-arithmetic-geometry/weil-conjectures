/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurveWeil.CurveSupportHeartDefs
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension

/-! # A step of the smooth-curve support-heart proof -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ell : ℕ) [Fact ell.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hbase : Finite k ∨ IsAlgClosed k)
  (C : Over (Spec (.of k))) [Smooth C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ell
local notation "R" => condensedRingObj Λ C.left
local notation "B" => BoundedConstructible R
local notation "M" => Mod (Sheaf (Scheme.ProEt.topology C.left) Ab) R
local notation "H" => DerivedCategory.homologyFunctor M
local notation "Perv" => FiniteOrClosedPerverseHeart ell hbase C
local notation "Punctual" => CondensedCurvePerverse.IsPunctual Λ C.left
local notation "NoPunctual" => CondensedCurvePerverse.HasNoPunctualSubsheaf Λ C.left

/-- Support and cosupport on a smooth curve have the cohomological descriptions.
Source: current blueprint thm-a1-curve-perverse-heart.proof.md, Steps 0--3;
Wei Yang #1441, item 36 (finite or algebraically closed base).
(blueprint: lem-dl-a1-curve-support-description)

Proof: choose a dense open on which the finitely many cohomology sheaves are lisse.
The support inequality in positive cohomological degrees forces vanishing; degree zero
forces finite closed support, and all remaining inequalities follow from dimension one.
Lattice reductions show that lisse sheaves have no punctual subsheaves. Smooth purity
identifies the dualizing object on the open with the Tate twist shifted by two, and on
the finite closed complement with the coefficient unit. Residue fields are still finite
or algebraically closed. Tensor duality and induction on standard truncations compute
cohomology of the dual. Closed-costalk duality identifies the closed restriction of the
dual with the dual of the costalk. The canonical localization triangle identifies its
bottom cohomology with the kernel of F → j_*j^*F, the maximal punctual subsheaf.
Thus cosupport is exactly vanishing below -1 and absence of punctual subobjects in H^-1.
The sheaf predicates include constructibility, inherited from bounded constructibility. -/
theorem curveSupportDescription_on_curve (hpure : C.left.IsPureDimension 1) :
    CurveSupportDescription ell hbase C := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
