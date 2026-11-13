/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fintype.Sort
import WeilConjectures.Mathlib.RingTheory.Smooth.Local

/-!
# Invertible Jacobian presentations near regular closed points

## References

* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [Stacks Project, Tag 00TS](https://stacks.math.columbia.edu/tag/00TS)
-/

@[expose] public section

universe u v

namespace Algebra

set_option linter.unusedVariables false in
/-- A regular closed point has a principal neighbourhood with an explicit polynomial
presentation and an invertible Jacobian minor. This statement concerns equations and
an algebra isomorphism; it does not assert smoothness. -/
theorem exists_jacobian_unit_presentation_of_regularAtMaximal
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsAlgClosed k] [Algebra.FiniteType k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    ∃ (g : S), g ∉ m ∧
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
        (e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k]
          Localization.Away g) (i : Fin c → Fin n),
        StrictMono i ∧ IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range f))
          (Matrix.det (fun j l : Fin c ↦ MvPolynomial.pderiv (i l) (f j)))) := by
  classical
  have : m.IsMaximal := hm
  have : IsRegularLocalRing (Localization.AtPrime m) := hreg
  have : IsSmoothAt k m := IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed m
  have : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨g, hg, hstd⟩ := IsSmoothAt.exists_notMem_isStandardSmooth k m
  have : IsStandardSmooth k (Localization.Away g) := hstd
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd.out
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype σ := Fintype.ofFinite σ
  let Q := P.reindex (Fintype.equivFin ι).symm (Equiv.refl σ)
  let : LinearOrder σ := LinearOrder.lift' Q.map Q.map_inj
  let r : Fin (Fintype.card σ) ≃o σ := monoEquivOfFin σ rfl
  let T := Q.reindex (Equiv.refl _) r.toEquiv
  have hi : StrictMono T.map := by
    intro a b hab
    exact r.strictMono hab
  let equiv := T.toPresentation.quotientEquiv.restrictScalars k
  have hu : IsUnit (Ideal.Quotient.mk T.ker T.jacobiMatrix.det) := by
    apply (MulEquiv.isUnit_map (f := equiv.toRingEquiv.toMulEquiv)).mp
    change IsUnit (algebraMap T.Ring (Localization.Away g) T.jacobiMatrix.det)
    rw [← PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    exact T.jacobian_isUnit
  refine ⟨g, hg, Fintype.card ι, Fintype.card σ, T.relation, ?_, T.map, hi, ?_⟩
  · rw [T.toPresentation.span_range_relation_eq_ker]
    exact equiv
  · have hmatrix : (fun j l : Fin (Fintype.card σ) ↦
        MvPolynomial.pderiv (T.map l) (T.relation j)) = T.jacobiMatrix.transpose := by
      apply Matrix.ext
      intro j l
      exact (PreSubmersivePresentation.jacobiMatrix_apply T.toPreSubmersivePresentation l j).symm
    rw [hmatrix, Matrix.det_transpose, T.toPresentation.span_range_relation_eq_ker]
    exact hu

end Algebra
