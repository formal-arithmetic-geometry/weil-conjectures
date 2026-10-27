/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.AlgebraicGeometry.RegularJetMatrix
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Descent and support of coefficient derivative ideals -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- A regular ideal whose straightened Taylor extension is the coefficient-derivative
ideal agrees locally with its regular inverse image at a coefficient-order point.

Source: BM 1997, Remark 9.5 and completion of Theorem 9.6, pp.277,282;
steps 4--5 of the coefficient-order comparison, with the residue-field diagonal
interpretation supplied by implicit Taylor calculus and Taylor normal-cone splitting
(blueprint: lem-trf-coefficient-derivative-ideal-descent).

Proof: The center is on the coefficient-order locus by hypothesis. The bounds
on gamma and delta give finite sets of indices, since there are
finitely many variables and vertices. On the smooth closed affine scheme N their
regular derivatives generate a coherent ideal C. Its inverse image I in U contains
the equations of N. Both I and the given ideal J are finitely generated, as U is
affine of finite type over a field. The implicit-coordinate calculus identifies
restriction to N with setting Z=0, sends its equations to (Z), and commutes with
tangential differentiation. Therefore the Taylor extension of I is exactly the
right side of the assumed formal equality. The straightened Taylor map is the
faithfully flat local Taylor map followed by an automorphism. Contracting equality
of extended ideals gives equality at the stalk of j(b0). Coherence spreads this to
one open neighbourhood, giving the displayed equality of ideal sheaves.
At any b in N, the Taylor normal-cone comparison detects maximal-ideal powers:
a germ belongs to m_b^h iff its Taylor series has no terms of degree below h.
For the reverse implication, a first nonzero graded part of degree less than h
would remain nonzero after the injective normal-cone comparison. The coefficient
of degree delta is evaluation of the delta-th regular derivative divided by delta!.
All factorials are units, so these order conditions are precisely vanishing of C.
The inverse image ideal I also cuts out N; its zero locus in U is exactly the
image of these coefficient-order points. Equality of ideal sheaves on the chosen
open makes this equivalent to J lying in the evaluation kernel there. This uses
actual stalk maximal ideals, including nonclosed points; empty index sets give
C=0 and the same inverse-image and support argument. -/
theorem coefficient_derivative_ideal_descent
    {k : Type u} [Field k] [CharZero k]
    (U N : Scheme.{u}) [IsAffine U]
    (p : U ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (j : N ⟶ U) [IsClosedImmersion j] [Smooth (j ≫ p)]
    (b₀ : N) {m n s : ℕ}
    (coord : MvPolynomial (Fin m ⊕ Fin n) k →+* Γ(U, ⊤))
    (hetale : Etale (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom coord)))
    (hover : U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (coord.comp MvPolynomial.C)) = p)
    (w : MvPolynomial (Fin m) k →+* Γ(N, ⊤))
    (hw : w = j.appTop.hom.comp (coord.comp (MvPolynomial.rename Sum.inl).toRingHom))
    (hetaleW : Etale (N.toSpecΓ ≫ Spec.map (CommRingCat.ofHom w)))
    (der : (Fin m ⊕ Fin n) → Derivation ℤ Γ(U, ⊤) Γ(U, ⊤))
    (hderk : ∀ (l : Fin m ⊕ Fin n) (r : k), der l (coord (MvPolynomial.C r)) = 0)
    (hderx : ∀ l r : Fin m ⊕ Fin n,
      der l (coord (MvPolynomial.X r)) = if l = r then 1 else 0)
    (derW : Fin m → Derivation ℤ Γ(N, ⊤) Γ(N, ⊤))
    (hderWk : ∀ (l : Fin m) (r : k), derW l (w (MvPolynomial.C r)) = 0)
    (hderWw : ∀ l r : Fin m, derW l (w (MvPolynomial.X r)) = if l = r then 1 else 0)
    (equations : Fin n → Γ(U, ⊤))
    (hequations : RingHom.ker j.appTop.hom = Ideal.span (Set.range equations))
    (hjacobian : ∀ b : N, IsUnit (Matrix.det (fun l r : Fin n ↦
      N.Γevaluation b (j.appTop (der (Sum.inr r) (equations l))))))
    (TN : ∀ b : N, Γ(N, ⊤) →+* MvPowerSeries (Fin m) (N.residueField b))
    (hTN : ∀ b : N, isTaylorMap w (N.Γevaluation b).hom (TN b))
    (straight : ∀ b : N, Γ(U, ⊤) →+*
      MvPowerSeries (Fin m ⊕ Fin n) (N.residueField b))
    (hres : ∀ (b : N) (r : Γ(U, ⊤)),
      MvPowerSeries.constantCoeff (straight b r) = N.Γevaluation b (j.appTop r))
    (hk : ∀ (b : N) (r : k), straight b (coord (MvPolynomial.C r)) =
      MvPowerSeries.C (N.Γevaluation b (j.appTop (coord (MvPolynomial.C r)))))
    (hW : ∀ (b : N) (l : Fin m), straight b (coord (MvPolynomial.X (Sum.inl l))) =
      MvPowerSeries.C (N.Γevaluation b (w (MvPolynomial.X l))) +
        MvPowerSeries.X (Sum.inl l))
    (hZ : ∀ (b : N) (l : Fin n), straight b (coord (MvPolynomial.X (Sum.inr l))) =
      MvPowerSeries.rename Sum.inl (TN b (j.appTop (coord (MvPolynomial.X (Sum.inr l))))) +
        MvPowerSeries.X (Sum.inr l))
    (α : Fin s → Fin n →₀ ℕ)
    (coeff : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤))
    (hcenter : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      N.presheaf.germ ⊤ b₀ (by trivial) (coeff l γ) ∈
        IsLocalRing.maximalIdeal (N.presheaf.stalk b₀) ^ ((α l).degree - γ.degree))
    (J : Ideal Γ(U, ⊤))
    (hJ : Ideal.map (straight b₀) J =
      Ideal.span (Set.range fun l : Fin n ↦
        (MvPowerSeries.X (Sum.inr l) :
          MvPowerSeries (Fin m ⊕ Fin n) (N.residueField b₀))) ⊔
      Ideal.span {g | ∃ (l : Fin s) (γ : Fin n →₀ ℕ) (δ : Fin m →₀ ℕ),
        γ.degree < (α l).degree ∧ δ.degree < (α l).degree - γ.degree ∧
          g = MvPowerSeries.rename Sum.inl (iteratedPartial δ (TN b₀ (coeff l γ)))}) :
    ∃ V : U.Opens, j b₀ ∈ V ∧
      (∀ y : U, y ∈ V →
        ((∃ b : N, j b = y ∧ ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
          γ.degree < (α l).degree →
            N.presheaf.germ ⊤ b (by trivial) (coeff l γ) ∈
              IsLocalRing.maximalIdeal (N.presheaf.stalk b) ^ ((α l).degree - γ.degree)) ↔
          J ≤ RingHom.ker (U.Γevaluation y).hom)) ∧
      (Scheme.IdealSheafData.ofIdealTop J).comap V.ι =
        (Scheme.IdealSheafData.ofIdealTop (Ideal.comap j.appTop.hom
          (Ideal.span {h | ∃ (l : Fin s) (γ : Fin n →₀ ℕ) (δ : Fin m →₀ ℕ),
            γ.degree < (α l).degree ∧ δ.degree < (α l).degree - γ.degree ∧
              h = regularIteratedPartial derW δ (coeff l γ)}))).comap V.ι := by sorry

end AlgebraicGeometry.HilbertCoefficient
