/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JacobianPresentationLift
public import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import WeilConjectures.RingTheory.EtaleAlgebraLiftEtaleFP
import WeilConjectures.RingTheory.EtaleAlgebraLiftReduction

/-!
# Étale algebras lift across arbitrary quotients

## Main statements

- `Algebra.SquareJacobianPresentation.CoefficientLift.etale_and_reduction_equiv`: the explicit
  lifted quotient is étale of finite presentation, and its specified reduction is an isomorphism.
- `Algebra.exists_etale_coefficientLift`: every étale quotient algebra admits such a lift.

## Implementation details

The lifted relations together with `t * Δ - 1` have Jacobian determinant `Δ²`, a unit in the
lifted quotient, so the square Jacobian criterion gives étaleness. Modulo the extended ideal,
`t` is forced to be the inverse of `Δ`, which yields the reduction isomorphism. No step uses
nilpotence of the ideal.

## References

* [Stacks: Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public section

universe u v

namespace Algebra

/-- The lifted Jacobian quotient is étale of finite presentation, and the specified reduction
induces an isomorphism modulo the extended ideal. -/
theorem SquareJacobianPresentation.CoefficientLift.etale_and_reduction_equiv
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra (A ⧸ I) B] {m : ℕ}
    (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
    (L : Algebra.SquareJacobianPresentation.CoefficientLift I P) :
    Algebra.Etale A L.LiftRing ∧ Algebra.FinitePresentation A L.LiftRing ∧
      ∃ e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B,
        ∀ x : L.LiftRing,
          e (Ideal.Quotient.mk (I.map (algebraMap A L.LiftRing)) x) = L.reduction x := by
  obtain ⟨hef, hfp⟩ := coefficientLift_etale_fp I P L
  obtain ⟨e, he⟩ := coefficientLift_reduction_equiv I P L
  exact ⟨hef, hfp, e, he⟩

/-- Every étale finite-presentation algebra over an arbitrary quotient admits the explicit
Jacobian lift and its reduction isomorphism. -/
theorem exists_etale_coefficientLift
    {A : Type u} [CommRing A] (I : Ideal A)
    (B : Type v) [CommRing B] [Algebra (A ⧸ I) B] [Algebra.Etale (A ⧸ I) B] :
    ∃ (m : ℕ) (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
      (L : Algebra.SquareJacobianPresentation.CoefficientLift I P),
      Algebra.Etale A L.LiftRing ∧ Algebra.FinitePresentation A L.LiftRing ∧
        ∃ e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B,
          ∀ x : L.LiftRing,
            e (Ideal.Quotient.mk (I.map (algebraMap A L.LiftRing)) x) = L.reduction x := by
  classical
  obtain ⟨ι, hι, ⟨P⟩⟩ :=
    Etale.iff_exists_squareJacobianPresentation.mp (inferInstance : Etale (A ⧸ I) B)
  let e : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  let Q : SquareJacobianPresentation (A ⧸ I) B (Fin (Nat.card ι)) :=
    { P.toSubmersivePresentation.reindex e e with
      map_eq_id := by
        ext i
        simp [SubmersivePresentation.reindex, PreSubmersivePresentation.reindex,
          P.map_eq_id] }
  have hs := MvPolynomial.map_surjective (σ := Fin (Nat.card ι))
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  choose f hf using fun i => hs (Q.relation i)
  let L : SquareJacobianPresentation.CoefficientLift I Q := ⟨f, hf⟩
  exact ⟨Nat.card ι, Q, L, L.etale_and_reduction_equiv I Q⟩

end Algebra
