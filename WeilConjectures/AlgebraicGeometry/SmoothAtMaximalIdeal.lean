/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.AlgebraicGeometry.MaximalIdealDifferentialCotangentDimension
import WeilConjectures.AlgebraicGeometry.RegularMaximalJacobianPresentation
public import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Smoothness at a maximal ideal from a differential dimension bound

## References

* [Stacks Project, Tag 00TS](https://stacks.math.columbia.edu/tag/00TS)
-/

@[expose] public section

universe u v

namespace Algebra

/-- Over an algebraically closed field, the differential dimension bound at a maximal ideal
implies smoothness there. -/
theorem smoothAtMaximalIdeal_of_finrank_differentials_le_krullDim
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsAlgClosed k] [Algebra.FiniteType k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (h : ((Module.finrank (m.ResidueField)
      (TensorProduct S m.ResidueField (KaehlerDifferential k S)) : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime m)) :
    ∃ g : S, g ∉ m ∧ Algebra.Smooth k (Localization.Away g) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hcot := finrank_cotangentSpace_atMaximal_eq_differentials k S m hm
  have hreg : IsRegularLocalRing (Localization.AtPrime m) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hcot]
    exact h
  obtain ⟨g, hg, n, c, f, e, i, hi, hunit⟩ :=
    exists_jacobian_unit_presentation_of_regularAtMaximal k S m hm hreg
  let P := PreSubmersivePresentation.naive (v := f) i hi.injective
  have hP : IsUnit P.jacobian := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hmatrix : P.jacobiMatrix =
        Matrix.transpose (fun j l : Fin c ↦ MvPolynomial.pderiv (i l) (f j)) := by
      ext j l : 1
      exact PreSubmersivePresentation.jacobiMatrix_naive i hi.injective _ _ j l
    rw [hmatrix, Matrix.det_transpose]
    exact hunit
  let Q : SubmersivePresentation k
      (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) (Fin n) (Fin c) :=
    { toPreSubmersivePresentation := P, jacobian_isUnit := hP }
  have : IsStandardSmooth k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    Q.isStandardSmooth
  exact ⟨g, hg, Smooth.of_equiv e⟩

end Algebra
