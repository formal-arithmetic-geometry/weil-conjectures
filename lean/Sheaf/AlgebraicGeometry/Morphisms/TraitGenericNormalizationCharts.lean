/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Standard root charts for a generic Galois cover of a smooth trait family

Source: Stacks Project, Tags 0EYJ, 0EYG and 0EYH.
(blueprint: lem-sbc-trait-generic-normalization-charts)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Standard tame charts for the normalization of a generic Galois cover over a DVR.

Source: Stacks Project, Tag 0EYJ, first paragraph; Tags 0EYG and 0EYH.
(blueprint: lem-sbc-trait-generic-normalization-charts)

Proof: A DVR is Noetherian and regular. Smoothness makes L locally Noetherian and regular.
A uniformizer cuts out its closed fibre D as an effective Cartier divisor, since the
smooth morphism is flat. D is regular because it is smooth over the residue field.
The complement is the generic fibre. At a generic point of D its local ring is a DVR.
For each connected component of the generic torsor, use its stabilizer in G as the
Galois group. The ramification indices and residue degrees divide the stabilizer order
(Tag 09EB). They therefore divide the invertible order of G. The inseparable residue
extension has degree a power of the residue characteristic, so its degree is one.
Consequently the generic cover is tame in codimension one. Tag 0EYG gives an affine
etale neighbourhood of each point on which the punctured cover is a finite disjoint
union of standard root covers, all using the same equation for D. Tag 0EYH identifies
its normalization with the full standard root covers. Normalization commutes with
etale base change (03GE, 03GV), giving isomorphisms over each affine neighbourhood.
Finite disjoint unions of affine spectra are spectra of product rings. Enumerate the
finite component set by Fin m. Outside D split the finite etale cover etale locally and
use e = 1, f = 1. The empty family of
components gives m = 0 and the zero product ring. No section is required. -/
theorem GaloisCover.trait_generic_normalization_chart
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A))
    [QuasiCompact d] [QuasiSeparated d] [Smooth d]
    (G : Type (u + 1)) [Group G] [Finite G] (hG : IsUnit (Nat.card G : A))
    (W : GaloisCover G (pullback d (Spec.map (CommRingCat.ofHom (algebraMap A K))))) :
    letI : IsFinite W.π := W.isFinite
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    let p := W.π ≫ pullback.fst d b
    IsFinite p.fromNormalization → ∀ x : L,
      ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
        Etale φ ∧ φ y = x ∧
        ∃ (m : ℕ) (f : R) (e : Fin m → ℕ),
          (∀ k, 0 < e k ∧ IsUnit (e k : R)) ∧
          ∃ α : pullback p.fromNormalization φ ≅
            Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))) =
              pullback.snd p.fromNormalization φ := by sorry

end AlgebraicGeometry.Scheme
