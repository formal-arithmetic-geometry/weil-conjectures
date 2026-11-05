/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Topology.JacobsonSpace

/-!
# StalkAlgebraic

Ported from the `proetale` package (`Proetale.Algebra.StalkAlgebraic`).
-/

@[expose] public section

/-- `IsScalarTower` version of `Subalgebra.isField_of_algebraic`. -/
lemma IsField.of_isScalarTower_of_isAlgebraic (k R K : Type*) [Field k] [Field K]
    [CommSemiring R] [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic k K] : IsField R :=
  AlgEquiv.ofInjective (IsScalarTower.toAlgHom k R K)
    (FaithfulSMul.algebraMap_injective R K) |>.isField <| Subalgebra.isField_of_algebraic _

/-- If `q` lies over a maximal ideal `m` and the residue field extension is algebraic, `q`
is maximal. -/
@[stacks 00GA]
lemma Ideal.IsMaximal.of_isAlgebraic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [Ideal.IsPrime q]
    [q.LiesOver m]
    [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra m q]
    [Algebra.IsAlgebraic m.ResidueField q.ResidueField] : q.IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  let := Ideal.Quotient.field m
  let lf : m.ResidueField →+* B ⧸ q :=
    IsLocalization.lift (M := nonZeroDivisors _ ) (g := algebraMap (A ⧸ m) (B ⧸ q))
      fun y ↦ (isUnit_of_mem_nonZeroDivisors y.2).map _
  algebraize [lf]
  have h : IsScalarTower m.ResidueField (B ⧸ q) q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (A ⧸ m))
    rw [← RingHom.cancel_right Ideal.Quotient.mk_surjective]
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra lf, lf,
      IsLocalization.lift_eq]
    rw [Ideal.algebraMap_quotient_residueField_mk, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ B]
    rfl
  have h : FaithfulSMul (B ⧸ q) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]
    apply IsFractionRing.injective
  exact .of_isScalarTower_of_isAlgebraic m.ResidueField (B ⧸ q) q.ResidueField

