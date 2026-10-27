/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.RingTheory.FormalInitialDiagram
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Regular Taylor minors in straightened coordinates -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- A single Taylor-degree cutoff controls the Hilbert equality germ and the
Taylor extension of the regular minors, for every regular generating list.

Source: BM 1997, Theorem 7.14, Remarks 9.1 and 9.5, completion of Theorem 9.6,
pp.265--268,275--277,282; steps 1--2 of the coefficient-order comparison
(blueprint: lem-trf-straightened-regular-stratum-comparison).

Proof: Supported division identifies the central truncated quotient with the
complementary monomials of D. The jet-diagram theorem makes the extended Hilbert
functions a finite set on an affine neighbourhood. Choose, for each different
function, one degree distinguishing it from the central function; take the maximum
of these degrees and the vertex orders minus one. The regular-stratum theorem
identifies vanishing of the cumulative minors with equality of these functions
near the center: shrink where a central rank-sized minor in each degree is a unit.
Use one finite generating list first. Any other list generates the same translated
truncated ideal, so presentation Fitting independence gives exactly the same minors
in every degree. Thus the cutoff is independent of the generating list.
The straightening is the invertible triangular formal change fixing W and sending
the original transverse coordinates to their restricted Taylor series plus Z.
For each truncation substitute F(X+Y)-F(X) in the translation variables Y.
Its inverse comes from the inverse coordinate change, so it gives an invertible
linear change of presentation. Fitting invariance and the regular Taylor-minor
base-change theorem identify the extension with the formal stratum ideal of f.
Ordered minimal vertices give the nondecreasing degrees and incomparability required
by the formal-minors theorem. Apply that theorem, using the central block and
later-derivative hypotheses, to obtain the low-derivative ideal for every permitted
cutoff. Zero fibre dimension uses oversized minors, both zero. Empty vertex lists
and empty variable sets use the same presentations. -/
theorem straightened_regular_stratum_comparison
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
    (f : ∀ b : N, Fin s → MvPowerSeries (Fin m ⊕ Fin n) (N.residueField b))
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
        inDiagram α d δ → iteratedPartial (fullVertex m δ) (f b l) ∈ transverseIdeal α d) :
    ∃ q₀ : ℕ, (∀ l : Fin s, (α l).degree - 1 ≤ q₀) ∧
      ∀ q : ℕ, q₀ ≤ q → ∀ (r : ℕ) (generators : Fin r → Γ(U, ⊤)),
        Ideal.span (Set.range generators) = RingHom.ker i.appTop.hom →
        ∃ V : U.Opens, i a ∈ V ∧
          (∀ y : U, y ∈ V →
            ((⨆ t ∈ Finset.range (q + 1),
              regularJetMinorIdeal coord der generators (U.Γevaluation (i a)).hom t) ≤
                RingHom.ker (U.Γevaluation y).hom ↔
              ∀ t : ℕ, extendedHilbert
                (taylorIdeal (RingHom.ker i.appTop.hom) (TU y)) t =
                  (MonomialDiagram.hilbertCount D t : ℕ∞))) ∧
          Ideal.map (straight b₀)
            (⨆ t ∈ Finset.range (q + 1),
              regularJetMinorIdeal coord der generators (U.Γevaluation (i a)).hom t) =
            lowDerivativeIdeal α (f b₀) := by sorry

end AlgebraicGeometry.HilbertCoefficient
