/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Normal root models containing a generic trait torsor as a dense open

Source: Stacks Project, Tags 0EYJ, 09EB, 0EYG and 0EYH.
(blueprint: lem-sbc-trait-generic-root-model)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A tame generic torsor admits local normal integral root models before normalization.

Source: Stacks Project, Tag 0EYJ, trait paragraph; Tags 09EB, 0EYG and 0EYH.
(blueprint: lem-sbc-trait-generic-root-model)

Proof: The smooth total space over the DVR is regular and locally Noetherian.
Its closed fibre is a regular effective Cartier divisor, cut out by a uniformizer;
flatness identifies the complement with the generic fibre. At its generic points
ramification indices and inseparable residue degrees divide the order of the
stabilizer of a connected component of the torsor, hence the invertible order of G.
Thus the cover is tame in codimension one. Tag 0EYG supplies an affine etale
neighborhood and a finite product of punctured root algebras with a common equation
f for the divisor and positive invertible exponents. Form the full monic root
algebras explicitly; their spectra are finite, hence integral, over Spec R.
Away from f they are the prescribed punctured root covers. At primes over f their
local rings are regular: quotienting by the root coordinate gives the regular
closed fibre, and that coordinate is a nonzerodivisor. Away from f they are etale
over the regular base, hence regular too. Therefore all local rings are normal
domains. Finite products preserve this stalk assertion and are Noetherian.
The open where f is invertible is dense since f is a nonzerodivisor in each monic
root algebra. The punctured-cover isomorphism gives gamma onto that open over R.
Off the closed fibre, split the etale cover etale locally and use f = 1, e = 1.
Empty products give the empty spectrum and the unique empty open and isomorphism;
no connectedness or nonemptiness hypothesis is needed. No normalization is used. -/
theorem GaloisCover.trait_generic_root_model
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
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap R (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
        (∀ z : N, IsDomain (N.presheaf.stalk z) ∧
          IsIntegrallyClosed (N.presheaf.stalk z)) ∧
        ∃ V : N.Opens, Dense (V : Set N) ∧
          ∃ γ : pullback p φ ≅ V.toScheme,
            γ.hom ≫ V.ι ≫ q = pullback.snd p φ := by sorry

end AlgebraicGeometry.Scheme
