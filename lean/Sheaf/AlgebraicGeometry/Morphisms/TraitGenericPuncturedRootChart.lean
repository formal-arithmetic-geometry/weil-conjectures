/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-! Punctured Kummer charts before normality. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Punctured Kummer charts for a generic torsor over a smooth trait family.

Source: Stacks Project, Tags 0EYJ (first trait paragraph), 09EB and 0EYG.
(blueprint: lem-sbc-trait-generic-punctured-root-chart)

Proof: A DVR is regular Noetherian, and a smooth scheme over it is regular and
locally Noetherian. Its closed fibre is smooth over the residue field, hence
regular, and flatness makes a uniformizer a nonzerodivisor defining that fibre.
The complement is the generic fibre. At each generic point of the closed fibre
apply 09EB to each connected torsor component and its stabilizer in G. The
ramification indices and inseparable residue degrees divide that stabilizer's
order, which divides the invertible order of G. Thus the cover is tame there.
Apply 0EYG to obtain an affine etale neighborhood and a finite disjoint union of
punctured root covers with common divisor equation f. Enumerate the factors by
Fin m, and identify their disjoint union with the basic open D(f) in the spectrum
of the product of full root algebras. This gives the isomorphism over Spec R and
its displayed compatibility. Etale pullback preserves regularity of the base
and divisor, and preserves the nonzerodivisor property by flatness. Consequently
R is regular, multiplication by f is injective, and R/(f) is regular. Outside
the closed fibre split the finite etale cover etale locally and take f=1 and all
exponents equal to one; the zero quotient is regular vacuously. Empty covers use
m=0. No normality or density of the full root model is asserted here. -/
theorem GaloisCover.trait_generic_punctured_root_chart
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A))
    [QuasiCompact d] [QuasiSeparated d] [Smooth d]
    (G : Type (u + 1)) [Group G] [Finite G] (hG : IsUnit (Nat.card G : A))
    (W : GaloisCover G (pullback d (Spec.map (CommRingCat.ofHom (algebraMap A K))))) :
    letI : IsFinite W.π := W.isFinite
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    let p := W.π ≫ pullback.fst d b
    ∀ x : L, ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
      Etale φ ∧ φ y = x ∧
      ∃ (m : ℕ) (f : R) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : R)) ∧
        IsRegularRing R ∧ IsSMulRegular R f ∧
        IsRegularRing (R ⧸ Ideal.span {f}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap R (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap R (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)) f)
        ∃ γ : pullback p φ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p φ := by sorry

end AlgebraicGeometry.Scheme
