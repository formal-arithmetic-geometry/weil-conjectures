/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalFrobeniusTrace

import Mathlib.FieldTheory.Finite.Basic

/-! # Degree divisibility for condensed local Frobenius powers

This proves the arithmetic component of the local Frobenius-power theorem.
(blueprint: lem-wf-condensed-local-frobenius-degree-divides).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The degree of the closed image of an `F_{q^m}`-point divides `m`.

Source: the finite-field degree argument in the opening sentence of the latest
`lem-wf-l2-upper.proof.md`, using the closed-point residue-field criterion.
Proof: the residue field of the closed image is finite over the base field. The given
point supplies an embedding of it into the chosen field with `q^m` elements. The `m`-th
power of its base-field Frobenius is the identity: after this embedding, this is the
finite-field identity `a^(q^m) = a`. Its Frobenius has order equal to the residue degree,
so that degree divides `m`. This avoids geometric evaluation or a choice of a cycle.
(blueprint: lem-wf-condensed-local-frobenius-degree-divides). -/
theorem condensed_local_frobenius_degree_divides
    (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (m : ℕ) (hm : 1 ≤ m) (x : D.extensionPoints Y₀ m hm)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (hxy : x.left (IsLocalRing.closedPoint (D.extensionSubfield m hm)) = y.val) :
    localClosedPointDegree D Y₀ y ∣ m := by
  let := Fintype.ofFinite D.k₀
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have : Module.Finite D.k₀ (Y₀.left.residueField y.val) :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.property
  have : Finite (Y₀.left.residueField y.val) := Module.finite_of_finite D.k₀
  have hc : Nat.card (D.extensionSubfield m hm) = D.q ^ m :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
  have : Finite (D.extensionSubfield m hm) := Nat.finite_of_card_ne_zero (by
    rw [hc, ← D.card_base]
    exact pow_ne_zero m Nat.card_pos.ne')
  let := Fintype.ofFinite (D.extensionSubfield m hm)
  let f : Y₀.left.residueField y.val →+* D.extensionSubfield m hm :=
    ((Y₀.left.residueFieldCongr hxy.symm).hom ≫
      (Scheme.SpecToEquivOfField (D.extensionSubfield m hm) Y₀.left x.left).2).hom
  change Module.finrank D.k₀ (Y₀.left.residueField y.val) ∣ m
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic D.k₀
    (Y₀.left.residueField y.val)]
  apply orderOf_dvd_of_pow_eq_one
  ext a
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    pow_iterate, AlgEquiv.one_apply]
  apply f.injective
  rw [map_pow]
  have hc' : Fintype.card D.k₀ ^ m = Fintype.card (D.extensionSubfield m hm) := by
    simpa only [← D.card_base, Nat.card_eq_fintype_card] using hc.symm
  rw [hc']
  exact FiniteField.pow_card (f a)

end WeilConjectures
