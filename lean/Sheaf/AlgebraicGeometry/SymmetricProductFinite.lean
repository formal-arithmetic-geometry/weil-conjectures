/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.AlgebraicGeometry.SymmetricProductProperties
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Finiteness of the symmetric-product morphism

Source: Weil conjectures blueprint, proper-base-change, reduction, symmetric-product-finite;
Stacks Project, proof of Tag 0A4F (blueprint: lem-weil-pbc-symmetric-product-finite).

The integer n is m + 1. The universal product cone gives the fibre power over S.
The endpoint b = 0 denotes D_+(T_0), with denominator y_i; b = 1 denotes D_+(T_n),
with denominator x_i. Polynomial variable i on the target denotes T_(i+1)/T_0
at the first endpoint and T_i/T_n at the second endpoint.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Classical in
/-- The symmetric-product map is finite. Its endpoint chart preimages have polynomial
coordinate rings in x_i/y_i and y_i/x_i, and the induced finite ring maps send coordinate
ratios to elementary symmetric polynomials. Each source variable satisfies the displayed
monic characteristic polynomial.

Source: blueprint symmetric-product-finite, statement and proof; Stacks Tag 0A4F
(blueprint: lem-weil-pbc-symmetric-product-finite).

Proof:
1. The target has the affine cover D_+(T_j) over affine base opens, by
   lemma-nagata-relative-affine-space-open-immersion and projective-space-base-change.
2. By projective-morphism-chart-preimage and symmetric-product-over-base the preimage is
   W = X_(F_j) intersect p_n^(-1)(V); the pulled ratios are F_l/F_j.
3. Expanding the coefficient polynomials gives F_j = sum_(|A|=n-j) M_A,
   M_A = product_(i in A) y_i product_(i not in A) x_i; X_(M_A) is U_A.
4. On W the functions M_A/F_j sum to 1. Their basic opens are principal opens in the
   affine charts U_A over V (p1-power-affine-charts), hence affine. Apply
   affine-unit-ideal-basic-opens (Stacks 01QF) to conclude that W is affine.
5. The affine-local-target criterion (01S8) makes sigma affine.
6. The fibre power is proper over S, by projective-space-base-change-proper and induction
   using proper-base-change and proper-composition. Projective space is separated over S.
   Apply proper-over-separated (01W6) to sigma, using symmetric-product-over-base.
7. Affine and universally closed implies integral (integral-univclosed, 01WM).
8. Integral and locally of finite type implies finite (integral-lft-finite, 01WJ).
9. At j=0 only M_all occurs, so W is the all-y chart. Divide the coefficient identity
   by product y_i to obtain T_l/T_0 = e_l(z). Each z_i is a root of product_k(T-z_k),
   whose expansion is T^n-e_1 T^(n-1)+...+(-1)^n e_n. The variables generate the
   polynomial algebra, so finite-of-integral-generators (02JJ) gives a finite ring map.
   At j=n interchange x and y: W is the all-x chart, and T_l/T_n = e_(n-l)(w).
   The same monic polynomial argument proves finiteness of this second ring map.
   For n>=2 the two endpoint charts do not cover the target; steps 1--8 use every chart.
-/
theorem symmetricProduct_finite (S : Scheme.{u}) (m : ℕ)
    (X : Over S)
    (pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{u} (Fin 2); S) ↘ S)))
    (_hprod : IsLimit (Fan.mk X pr))
    (hL : (symmetricProductLineBundle (fun i ↦ (pr i).left)).IsInvertible)
    (hs : Epi ((symmetricProductLineBundle (fun i ↦ (pr i).left)).freeHomEquiv.symm
      (symmetricProductCoordinateSection (fun i ↦ (pr i).left))))
    (σ : X.left ⟶ ℙ(ULift.{u} (Fin (m + 2)); S))
    (_hσ : σ = @ProjectiveSpace.homOfGeneratingSections.{u}
      (ULift.{u} (Fin (m + 2))) _ X.left S X.hom
      (symmetricProductLineBundle (fun i ↦ (pr i).left)) hL
      (symmetricProductCoordinateSection (fun i ↦ (pr i).left)) hs) :
    IsFinite σ ∧
    ∀ (V : S.Opens) (R : CommRingCat.{u}) (eV : V.toScheme ≅ Spec R)
      (b : Fin 2) (U : (ℙ(ULift.{u} (Fin (m + 2)); S)).Opens)
      (hU : U = ProjectiveSpace.standardOpen _ S
        (ULift.up (if b = 0 then 0 else Fin.last (m + 1))) ⊓
          (ℙ(ULift.{u} (Fin (m + 2)); S) ↘ S) ⁻¹ᵁ V),
      (σ ⁻¹ᵁ U : Set X.left) =
        (⋂ i : Fin (m + 1), Scheme.Modules.nonvanishingLocus
          (symmetricProductFactor (fun i ↦ (pr i).left) i)
          ((symmetricProductFactorSection (fun i ↦ (pr i).left) i
            (if b = 0 then 1 else 0)).val (op ⊤))) ∩
          X.hom.base ⁻¹' (V : Set S) ∧
      IsAffineOpen U ∧ IsAffineOpen (σ ⁻¹ᵁ U) ∧
      ∃ (h : U.toScheme ⟶ V.toScheme)
        (E : MvPolynomial (Fin (m + 1)) R ≃+* Γ(ℙ(ULift.{u} (Fin (m + 2)); S), U))
        (D : MvPolynomial (Fin (m + 1)) R ≃+* Γ(X.left, σ ⁻¹ᵁ U))
        (φ : MvPolynomial (Fin (m + 1)) R →+* MvPolynomial (Fin (m + 1)) R),
        h ≫ V.ι = U.ι ≫ (ℙ(ULift.{u} (Fin (m + 2)); S) ↘ S) ∧
        (∀ r : R, E (MvPolynomial.C r) =
          U.topIso.hom ((h ≫ eV.hom).appTop ((Scheme.ΓSpecIso R).inv r))) ∧
        (∀ i : Fin (m + 1), E (MvPolynomial.X i) =
          (ℙ(ULift.{u} (Fin (m + 2)); S)).presheaf.map
            (homOfLE (hU.symm ▸ inf_le_left)).op
              (ProjectiveSpace.coordRatio _ S
                (ULift.up (if b = 0 then 0 else Fin.last (m + 1)))
                (ULift.up (if b = 0 then i.succ else i.castSucc)))) ∧
        (∀ i : Fin (m + 1),
          (symmetricProductFactor (fun i ↦ (pr i).left) i).presheaf.map
            (homOfLE (le_top : σ ⁻¹ᵁ U ≤ ⊤)).op
              ((symmetricProductFactorSection (fun i ↦ (pr i).left) i
                (if b = 0 then 0 else 1)).val (op ⊤)) =
          D (MvPolynomial.X i) •
            (symmetricProductFactor (fun i ↦ (pr i).left) i).presheaf.map
              (homOfLE (le_top : σ ⁻¹ᵁ U ≤ ⊤)).op
                ((symmetricProductFactorSection (fun i ↦ (pr i).left) i
                  (if b = 0 then 1 else 0)).val (op ⊤))) ∧
        (∀ f : MvPolynomial (Fin (m + 1)) R, D (φ f) = σ.app U (E f)) ∧
        (∀ r : R, φ (MvPolynomial.C r) = MvPolynomial.C r) ∧
        (∀ i : Fin (m + 1), φ (MvPolynomial.X i) =
          MvPolynomial.esymm (Fin (m + 1)) R (if b = 0 then i.val + 1 else m + 1 - i.val)) ∧
        φ.Finite ∧
        (∏ i : Fin (m + 1),
          (Polynomial.X - Polynomial.C (MvPolynomial.X i) :
            Polynomial (MvPolynomial (Fin (m + 1)) R))) =
          ∑ k ∈ Finset.range (m + 2),
            Polynomial.C ((-1 : MvPolynomial (Fin (m + 1)) R) ^ k *
              MvPolynomial.esymm (Fin (m + 1)) R k) * Polynomial.X ^ (m + 1 - k) ∧
        (∏ i : Fin (m + 1),
          (Polynomial.X - Polynomial.C (MvPolynomial.X i) :
            Polynomial (MvPolynomial (Fin (m + 1)) R))).Monic ∧
        ∀ i : Fin (m + 1),
          Polynomial.eval (MvPolynomial.X i)
            (∏ k : Fin (m + 1),
              (Polynomial.X - Polynomial.C (MvPolynomial.X k) :
                Polynomial (MvPolynomial (Fin (m + 1)) R))) = 0 := by
  sorry

end AlgebraicGeometry
