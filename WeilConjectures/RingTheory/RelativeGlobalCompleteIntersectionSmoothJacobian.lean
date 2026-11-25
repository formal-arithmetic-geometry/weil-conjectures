/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Module
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionConormalFree
import WeilConjectures.RingTheory.SmoothLocalizationConormalSplit

/-!
# The Jacobian criterion for a relative global complete intersection

We prove the Jacobian criterion: a relative global complete intersection `R[x₁, ..., xₙ]/(f)` is
smooth over `R` at a prime if and only if some maximal minor of the Jacobian matrix of `f` does
not lie in that prime.

## References

* [Stacks, Tag 00TE]
-/

@[expose] public section

universe v

namespace Algebra

-- The presentation-composition API packages the extra variable and block determinant.
private theorem smooth_jacobian_localization
    {R : Type v} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (i : Fin c → Fin n) (hi : Function.Injective i) :
    Smooth R (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range f))
        (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j))))) := by
  classical
  let P := PreSubmersivePresentation.naive (v := f) i hi
  let g := Ideal.Quotient.mk (Ideal.span (Set.range f))
    (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j)))
  have hP : P.jacobian = g := by
    rw [P.jacobian_eq_jacobiMatrix_det]
    have hmat : P.jacobiMatrix =
        Matrix.transpose (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j)) := by
      ext j k
      simp [P, PreSubmersivePresentation.jacobiMatrix_naive, Matrix.transpose_apply]
    rw [hmat, Matrix.det_transpose]
    rfl
  let Q := PreSubmersivePresentation.localizationAway (Localization.Away g) g
  let T : SubmersivePresentation R (Localization.Away g)
      (Unit ⊕ Fin n) (Unit ⊕ Fin c) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, hP,
          PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit g).mul
          (IsLocalization.Away.algebraMap_isUnit g) }
  let := T.isStandardSmooth
  infer_instance

-- Localize the equation basis and take matrices of the differential and its left inverse.
private theorem jacobian_left_inverse_of_smooth_localization
    {R : Type v} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (hci : IsRelativeGlobalCompleteIntersectionPresentation f)
    (g : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
    [Smooth R (Localization.Away g)] :
    ∃ B : Matrix (Fin c) (Fin n) (Localization.Away g),
      B * (Matrix.of (fun i j ↦ algebraMap _ (Localization.Away g)
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.pderiv i (f j)))) :
          Matrix (Fin n) (Fin c) (Localization.Away g)) =
          1 := by
  classical
  let I := Ideal.span (Set.range f)
  let S := MvPolynomial (Fin n) R ⧸ I
  let G := Localization.Away g
  obtain ⟨⟨b, hb⟩, _, _⟩ := relativeGlobalCompleteIntersection_conormal_free f hci
  let bg := b.ofIsLocalizedModule G (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) I.Cotangent)
  obtain ⟨d, π, hd, _, ⟨l, hl⟩, _⟩ := smooth_localization_conormal_split R n I g
  let e := Pi.basisFun G (Fin n)
  let A : Matrix (Fin n) (Fin c) G := LinearMap.toMatrix bg e d
  have hA : A = Matrix.of (fun i j ↦ algebraMap S G (Ideal.Quotient.mk I
      (MvPolynomial.pderiv i (f j)))) := by
    ext i j
    simp only [A, LinearMap.toMatrix_apply, e, Pi.basisFun_repr, bg,
      Module.Basis.ofIsLocalizedModule_apply]
    rw [hb j]
    exact hd ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩ i
  refine ⟨LinearMap.toMatrix e bg l, ?_⟩
  change LinearMap.toMatrix e bg l *
    (Matrix.of (fun i j ↦ algebraMap S G (Ideal.Quotient.mk I (MvPolynomial.pderiv i (f j)))) :
      Matrix (Fin n) (Fin c) G) = 1
  rw [← hA, ← LinearMap.toMatrix_comp, hl, LinearMap.toMatrix_id]

/-- A relative global complete intersection is smooth at a prime precisely when some maximal
Jacobian minor avoids that prime. A strictly increasing map `i : Fin c → Fin n` lists a subset
of size `c` in increasing order; rows of the determinant are equations and columns are `i k`. -/
theorem isSmoothAtPrime_iff_exists_jacobian_minor
    (R : Type v) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (hci : IsRelativeGlobalCompleteIntersectionPresentation f)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    IsSmoothAtPrime R q ↔
      ∃ i : Fin c → Fin n, StrictMono i ∧
        Ideal.Quotient.mk (Ideal.span (Set.range f))
          (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j))) ∉ q.asIdeal := by
  classical
  constructor
  · rintro ⟨g, hg, hs⟩
    let := hs
    let I := Ideal.span (Set.range f)
    let S := MvPolynomial (Fin n) R ⧸ I
    let G := Localization.Away g
    let A : Matrix (Fin n) (Fin c) G := Matrix.of fun i j ↦
      algebraMap S G (Ideal.Quotient.mk I (MvPolynomial.pderiv i (f j)))
    obtain ⟨B, hB⟩ := jacobian_left_inverse_of_smooth_localization f hci g
    change B * A = 1 at hB
    -- Cauchy–Binet works without c ≤ n: when c > n the sum is empty.
    have hsum := (Matrix.cauchy_binet c n B A).1
    rw [hB, Matrix.det_one] at hsum
    by_contra h
    push Not at h
    let J := q.asIdeal.map (algebraMap S G)
    have hminor (s : {s : Finset (Fin n) // s.card = c}) :
        (A.submatrix (s.val.orderEmbOfFin s.property) _root_.id).det ∈ J := by
      let i := s.val.orderEmbOfFin s.property
      have hi : StrictMono i := i.strictMono
      have hq := h i hi
      have hdet : (A.submatrix i _root_.id).det =
          algebraMap S G (Ideal.Quotient.mk I
            (Matrix.det (fun j k : Fin c ↦ MvPolynomial.pderiv (i k) (f j)))) := by
        let D : Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) R) :=
          Matrix.of fun j k ↦ MvPolynomial.pderiv (i k) (f j)
        have he : A.submatrix i _root_.id =
            ((algebraMap S G).comp (Ideal.Quotient.mk I)).mapMatrix D.transpose := by
          ext j k
          rfl
        rw [he, ← RingHom.map_det, Matrix.det_transpose]
        rfl
      rw [hdet]
      exact Ideal.mem_map_of_mem (algebraMap S G) hq
    have hone : (1 : G) ∈ J := by
      rw [hsum]
      apply Ideal.sum_mem
      intro s _
      exact J.mul_mem_left _ (hminor s)
    -- The prime avoids all powers of g, so its extended ideal is proper.
    have hproper : J ≠ ⊤ := by
      apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint
        (Submonoid.powers g) G q.asIdeal).mpr
      rw [Set.disjoint_left]
      intro x hx hqx
      obtain ⟨k, rfl⟩ := hx
      exact hg (q.isPrime.mem_of_pow_mem _ hqx)
    apply hproper
    rwa [Ideal.eq_top_iff_one]
  · rintro ⟨i, hi, hminor⟩
    exact ⟨_, hminor, smooth_jacobian_localization f i hi.injective⟩

end Algebra
