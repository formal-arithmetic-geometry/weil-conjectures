/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.RingTheory.FormalInitialDiagram
public import Sheaf.RingTheory.SupportedHomogeneousDivision
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

import Sheaf.AlgebraicGeometry.FormalLowDerivativeCoefficients
import Sheaf.AlgebraicGeometry.StraightenedRegularStratumComparison
import Sheaf.AlgebraicGeometry.CoefficientDerivativeIdealDescent
import Mathlib.Algebra.CharP.Algebra

/-! # Coefficient orders and the extended Hilbert equality germ

Source: Bierstone--Milman, Invent. Math. 128 (1997), Theorem 7.14,
Remarks 9.1, 9.5 and the completion of Theorem 9.6, pp.265--268,275--277,282;
ILO VIII 2.3.11--2.3.13 is the route reference
(blueprint: lem-trf-coefficient-order-hilbert-equality).

Taylor maps retain all relative coordinates, including at nonclosed points.
The regular conclusion is equality of actual ideal sheaves on one open neighbourhood.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

/-- The regular coefficient derivative ideal on the common coefficient scheme.
Only indices of total derivative order strictly below the assigned coefficient weight occur.
Source: BM 1997, Remark 9.5(1)
(blueprint: lem-trf-coefficient-order-hilbert-equality). -/
def coefficientDerivativeIdeal {m n s : ℕ} {A : Type u} [CommRing A]
    (α : Fin s → Fin n →₀ ℕ) (c : Fin s → (Fin n →₀ ℕ) → A)
    (D : Fin m → Derivation ℤ A A) : Ideal A :=
  Ideal.span {h | ∃ (i : Fin s) (γ : Fin n →₀ ℕ) (δ : Fin m →₀ ℕ),
    γ.degree < (α i).degree ∧ δ.degree < (α i).degree - γ.degree ∧
      h = regularIteratedPartial D δ (c i γ)}

open Classical in
/-- The coefficient order locus and the cumulative Taylor-minor locus have the same
extended Hilbert equality germ, and the same coherent ideal near the distinguished point.

Source: BM 1997, Theorem 7.14, Remarks 9.1, 9.5 and completion of Theorem 9.6,
pp.265--268,275--277,282
(blueprint: lem-trf-coefficient-order-hilbert-equality).

Proof (the six DAG steps):
1. Supported division and `lem-trf-jet-diagram-hilbert-control` identify the central
Hilbert function with the complementary monomial count and give finitely many local
values. Choose finitely many distinguishing degrees. The regular Taylor matrices of
any generators and `lem-trf-formal-hilbert-stratum-minors` give their equality germ.
2. The same theorem identifies their Taylor extension with the low derivative ideal.
Under a formal coordinate change T=F(W,Z), substitution of F(X+Y)-F(X) is invertible
on every truncated translation module. Thus `lem-trf-fitting-ideal-independence-base-change`
preserves its rank minors. If the fibre quotient has dimension zero the minors are oversized.
3. At the last block the vertex derivatives generate (Z): write g=UZ by assigning
monomials to their first Z factor. The constant Jacobian makes U invertible by its
geometric-series inverse and adjugate. Modulo (Z), mixed derivatives of f are factorials
times the W derivatives of its coefficients; characteristic zero makes these units.
This proves the displayed equality of formal derivative and coefficient ideals.
4. Form the finite regular coefficient derivative ideal on N and its inverse image on U.
Coordinate derivations commute with Taylor expansion by
`lem-trf-etale-coordinate-derivations-jacobian`. The implicit Taylor calculus identifies
restriction with Z=0 and extends the equations of N to (Z). Its faithful flatness
contracts the formal ideal equality to the stalk; coherence spreads it to one open.
5. By `lem-trf-taylor-normal-cone-splitting`, membership of a coefficient germ in the
h-th maximal-ideal power is equivalent to its Taylor series having order at least h,
also at nonclosed points. Taylor coefficients are regular derivatives divided by
factorials, so this is precisely the zero locus of the coefficient derivative ideal.
6. Intersect these finitely many neighbourhoods. This gives both loci and the coherent
ideal equality. For an empty list supported generation forces K=0, essentiality forces
n=0 and N=U locally. All derivative ideals vanish. Zero-dimensional ambient charts
use empty matrices; a degree-zero vertex is impossible at a point of X.
-/
theorem coefficient_order_hilbert_equality
    {k : Type u} [Field k] [CharZero k]
    (U X N : Scheme.{u}) [IsAffine U]
    (p : U ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    (i : X ⟶ U) [IsClosedImmersion i]
    (hcoherent : RingedSpace.IsCoherent U.toRingedSpace i.ker.toModules)
    (a : X) (j : N ⟶ U) [IsClosedImmersion j] [Smooth (j ≫ p)]
    (b₀ : N) (hb₀ : j b₀ = i a) {m n s : ℕ}
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
    (TU : ∀ y : U, Γ(U, ⊤) →+* MvPowerSeries (Fin m ⊕ Fin n) (U.residueField y))
    (hTU : ∀ y : U, isTaylorMap coord (U.Γevaluation y).hom (TU y))
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
    (α : Fin s → Fin n →₀ ℕ) (D : Set (Fin (m + n) →₀ ℕ))
    (hmonotone : MonomialDiagram.IsMonotone D)
    (hvertices : MonomialDiagram.IsOrderedVertexFamily D
      (fun l ↦ Finsupp.mapDomain finSumFinEquiv (fullVertex m (α l))))
    (hessential : ∀ l : Fin n, ∃ v : Fin s, 0 < α v l)
    (coeff : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤))
    (f : ∀ b : N, Fin s → MvPowerSeries (Fin m ⊕ Fin n) (N.residueField b))
    (hexpansion : ∀ (b : N) (l : Fin s) (d : (Fin m ⊕ Fin n) →₀ ℕ),
      MvPowerSeries.coeff d (f b l) =
        MvPowerSeries.coeff (Finsupp.comapDomain.addMonoidHom Sum.inl_injective d)
          (TN b (coeff l (Finsupp.comapDomain.addMonoidHom Sum.inr_injective d))))
    (hmember : ∀ (b : N) (l : Fin s),
      f b l ∈ taylorIdeal (RingHom.ker i.appTop.hom) (straight b))
    (horder : ∀ l : Fin s, (f b₀ l).order = ((α l).degree : ℕ∞))
    (hdivision : homogeneousDivision α (f b₀))
    (hgeneration : ∀ h ∈ taylorIdeal (RingHom.ker i.appTop.hom) (straight b₀),
      ∃ g : Fin s → MvPowerSeries (Fin m ⊕ Fin n) (N.residueField b₀),
        h = ∑ l : Fin s, g l * f b₀ l ∧
          ∀ l : Fin s, supported (g l) (inDelta (fun v ↦ fullVertex m (α v)) l))
    (hinitial : MonomialDiagram.initialDiagram
      (Ideal.map (MvPowerSeries.renameEquiv (N.residueField b₀) finSumFinEquiv).toRingHom
        (taylorIdeal (RingHom.ker i.appTop.hom) (straight b₀))) = D)
    (Q : ℕ) (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (hblocks : ∀ (b : N) (d : ℕ), (∃ l : Fin s, (α l).degree = d) →
      ∃ (pick : {l : Fin n // essential α d l} → Fin s)
        (β : {l : Fin n // essential α d l} → Fin n →₀ ℕ),
        (∀ l, α (pick l) = β l + Finsupp.single l.val 1 ∧
          (α (pick l)).degree ≤ d ∧
          iteratedPartial (fullVertex m (β l)) (f b (pick l)) ∈ transverseIdeal α d) ∧
        IsUnit (Matrix.det (fun l r : {l : Fin n // essential α d l} ↦
          MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (N.residueField b) (Sum.inr r.val)
            (iteratedPartial (fullVertex m (β l)) (f b (pick l)))))))
    (hlater : ∀ (b : N) (d : ℕ), (∃ l : Fin s, (α l).degree = d) →
      ∀ l : Fin s, d < (α l).degree → ∀ δ : Fin n →₀ ℕ,
        δ.degree ≤ Q → (∀ r : Fin n, δ r ≠ 0 → essential α d r) →
        inDiagram α d δ → iteratedPartial (fullVertex m δ) (f b l) ∈ transverseIdeal α d)
    (hcenter : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      N.presheaf.germ ⊤ b₀ (by trivial) (coeff l γ) ∈
        IsLocalRing.maximalIdeal (N.presheaf.stalk b₀) ^ ((α l).degree - γ.degree)) :
    ∃ q₀ : ℕ, (∀ l : Fin s, (α l).degree - 1 ≤ q₀) ∧
      ∀ q : ℕ, q₀ ≤ q → ∀ (r : ℕ) (generators : Fin r → Γ(U, ⊤)),
        Ideal.span (Set.range generators) = RingHom.ker i.appTop.hom →
        ∃ V : U.Opens, i a ∈ V ∧
          (∀ y : U, y ∈ V →
            ((∃ b : N, j b = y ∧ ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
              γ.degree < (α l).degree →
                N.presheaf.germ ⊤ b (by trivial) (coeff l γ) ∈
                  IsLocalRing.maximalIdeal (N.presheaf.stalk b) ^ ((α l).degree - γ.degree)) ↔
              ∀ t : ℕ, extendedHilbert
                (taylorIdeal (RingHom.ker i.appTop.hom) (TU y)) t =
                  (MonomialDiagram.hilbertCount D t : ℕ∞))) ∧
          (Scheme.IdealSheafData.ofIdealTop
            (⨆ t ∈ Finset.range (q + 1),
              regularJetMinorIdeal coord der generators (U.Γevaluation (i a)).hom t)).comap V.ι =
            (Scheme.IdealSheafData.ofIdealTop
              (Ideal.comap j.appTop.hom (coefficientDerivativeIdeal α coeff derW))).comap V.ι ∧
          Ideal.map (straight b₀)
            (⨆ t ∈ Finset.range (q + 1),
              regularJetMinorIdeal coord der generators (U.Γevaluation (i a)).hom t) =
            lowDerivativeIdeal α (f b₀) ∧
          lowDerivativeIdeal α (f b₀) =
            Ideal.span (Set.range fun l : Fin n ↦
              (MvPowerSeries.X (Sum.inr l) :
                MvPowerSeries (Fin m ⊕ Fin n) (N.residueField b₀))) ⊔
            Ideal.span {g | ∃ (l : Fin s) (γ : Fin n →₀ ℕ) (δ : Fin m →₀ ℕ),
              γ.degree < (α l).degree ∧ δ.degree < (α l).degree - γ.degree ∧
                g = MvPowerSeries.rename Sum.inl (iteratedPartial δ (TN b₀ (coeff l γ)))} := by
  classical
  let ρ : k →+* N.residueField b₀ :=
    (N.Γevaluation b₀).hom.comp (j.appTop.hom.comp (coord.comp MvPolynomial.C))
  let : CharZero (N.residueField b₀) := charZero_of_injective_ringHom ρ.injective
  have hformal := formal_lowDerivativeIdeal_eq_coefficients α hessential
    (fun l γ ↦ TN b₀ (coeff l γ)) (f b₀) (hexpansion b₀) (hblocks b₀)
  obtain ⟨q₀, hq₀, hstratum⟩ := straightened_regular_stratum_comparison
    U X N p i hcoherent a j b₀ hb₀ coord hetale hover w hw hetaleW der hderk hderx
    TU hTU TN hTN straight hres hk hW hZ α D hmonotone hvertices hessential f
    hmember horder hdivision hgeneration hinitial Q hQ hblocks hlater
  refine ⟨q₀, hq₀, ?_⟩
  intro q hq r generators hgenerators
  obtain ⟨V, haV, hV, hmap⟩ := hstratum q hq r generators hgenerators
  obtain ⟨W, hbW, hWlocus, hWideal⟩ := coefficient_derivative_ideal_descent
    U N p j b₀ coord hetale hover w hw hetaleW der hderk hderx
    derW hderWk hderWw equations hequations hjacobian TN hTN straight hres hk hW hZ
    α coeff hcenter (⨆ t ∈ Finset.range (q + 1),
      regularJetMinorIdeal coord der generators (U.Γevaluation (i a)).hom t)
    (hmap.trans hformal)
  refine ⟨V ⊓ W, ⟨haV, hb₀ ▸ hbW⟩, ?_, ?_, hmap, hformal⟩
  · intro y hy
    exact (hWlocus y hy.2).trans (hV y hy.1)
  · change (Scheme.IdealSheafData.ofIdealTop _).comap (V ⊓ W).ι =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.comap j.appTop.hom
        (Ideal.span _))).comap (V ⊓ W).ι
    have heq := congrArg
      (fun I : W.toScheme.IdealSheafData ↦
        I.comap (U.homOfLE (show V ⊓ W ≤ W from inf_le_right))) hWideal
    simpa only [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι] using heq

end AlgebraicGeometry.HilbertCoefficient
