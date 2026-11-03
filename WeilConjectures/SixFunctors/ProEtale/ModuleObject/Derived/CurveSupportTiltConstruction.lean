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

/-- Construct the tilt and its basic objects.
This statement does not assert abelianness, truncation endpoint membership, or either exact
sequence; those are derived in CurveSupportHeart.
Source: current blueprint thm-a1-curve-perverse-heart.proof.md, Steps 0, 4--5.
(blueprint: lem-dl-a1-curve-support-tilt-construction)

Proof: for a constructible sheaf F, choose a dense lisse open j and form the canonical
kernel F_p of F → j_*j^*F. It is the maximal punctual subobject, and F/F_p embeds in
the punctual-free sheaf j_*j^*F. Orthogonality for the proposed classes follows by
standard truncation and the vanishing of maps from punctual to punctual-free sheaves.
For K take the fibre of tau≤0 K → (H^0K/(H^0K)_p)[0]. The octahedral axiom produces
a truncation triangle; its cohomology satisfies the two classes in hdesc. Shifts supply
the indexed classes, and ordinary amplitude [a,b] gives perverse bounds [a,b+1].
The heart is their intersection. The ordinary direct image of a lisse sheaf along a
dense open has no punctual subobjects; closed point direct images are punctual.
Both remain constructible, so their indicated single complexes give the basic objects.
Standard truncation endpoint membership is proved separately in the parent theorem. -/
theorem curveSupportTiltConstruction (hpure : C.left.IsPureDimension 1)
    (hdesc : CurveSupportDescription ell hbase C) :
    ∃ t : TStructure B,
      (∀ n : ℤ, t.le n = FiniteOrClosedPerverseLE ell hbase C n) ∧
      (∀ n : ℤ, t.ge n = FiniteOrClosedPerverseGE ell hbase C n) ∧
      t.bounded = ⊤ ∧ Perv = t.heart ∧
      CurveSupportBasicObjects ell hbase C := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
