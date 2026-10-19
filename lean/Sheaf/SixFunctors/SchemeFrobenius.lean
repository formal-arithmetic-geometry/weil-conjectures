/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.Algebra.CharP.Invertible

/-!
# Scheme and Galois Frobenius of the geometric fibre

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, order 2415,
`def-trf-scheme-frobenius.md` (blueprint: def-trf-scheme-frobenius).

The q-power scheme Frobenius is the scalar extension of the model's relative Frobenius.
The Galois Frobenius maps are the geometric Frobenius automorphism and its inverse.
Derived pullbacks use the recorded finite, completed integral, rational and common-stage
coefficient operations, as well as the ordinary constant-ring specialization.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The scalar-extended q-power scheme Frobenius of a finite-type model.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius).
The map is the base change of the absolute q-power Frobenius supplied by
`relativeFrobenius`; its affine formula is `a ⊗ b ↦ a ^ q ⊗ b`. -/
noncomputable def schemeFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  D.relativeFrobenius X₀

/-- The m-fold iterate of the scalar-extended scheme Frobenius.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def schemeFrobeniusIterate
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  let Φ : End (D.geometricFiber X₀).left := D.schemeFrobenius X₀
  Φ ^ m

/-- Arithmetic Galois Frobenius on the geometric fibre, namely the inverse of
geometric Frobenius. Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def arithmeticGaloisFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  (D.geometricFrobenius X₀).inv

/-- Geometric Galois Frobenius on the geometric fibre.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def geometricGaloisFrobenius
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber X₀).left :=
  (D.geometricFrobenius X₀).hom

/-- The finiteness and radiciality assertions for the constructed Frobenius.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius); dependency
`lem-trf-scheme-frobenius-finite-radicial`.
Proof: unfold `schemeFrobenius`, which is the recorded scalar-extended relative
Frobenius, and apply `relativeFrobenius_isFinite_isRadicial` from that dependency. -/
theorem schemeFrobenius_isFinite_isRadicial
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsFinite (D.schemeFrobenius X₀) ∧
      UniversallyInjective (D.schemeFrobenius X₀) := by
  exact D.relativeFrobenius_isFinite_isRadicial X₀

/-- Derived pullback along the m-th scheme Frobenius on the small pro-etale site.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius); coefficient
conventions from `def-weil-derived-pullback-tensor-hom`. -/
noncomputable def schemeFrobeniusDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : Type u) [CommRing A] (m : ℕ) :
    Scheme.proEtaleDerivedCategory (D.geometricFiber X₀).left A ⥤
      Scheme.proEtaleDerivedCategory (D.geometricFiber X₀).left A :=
  Scheme.proEtaleConstantRingDerivedPullback A (D.schemeFrobeniusIterate X₀ m)

/-- Derived pullback along the m-th arithmetic Galois Frobenius.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius); coefficient
conventions from `def-weil-derived-pullback-tensor-hom`. -/
noncomputable def arithmeticGaloisDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : Type u) [CommRing A] (m : ℕ) :
    Scheme.proEtaleDerivedCategory (D.geometricFiber X₀).left A ⥤
      Scheme.proEtaleDerivedCategory (D.geometricFiber X₀).left A :=
  Scheme.proEtaleConstantRingDerivedPullback A
    (let Φ : End (D.geometricFiber X₀).left := D.arithmeticGaloisFrobenius X₀
    Φ ^ m)

/-- Derived pullback along the m-th geometric Galois Frobenius.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius); coefficient
conventions from `def-weil-derived-pullback-tensor-hom`. -/
noncomputable def geometricGaloisDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : Type u) [CommRing A] (m : ℕ) :
    Scheme.proEtaleDerivedCategory (D.geometricFiber X₀).left A ⥤
      Scheme.proEtaleDerivedCategory (D.geometricFiber X₀).left A :=
  Scheme.proEtaleConstantRingDerivedPullback A
    (let Φ : End (D.geometricFiber X₀).left := D.geometricGaloisFrobenius X₀
    Φ ^ m)

/-- The coefficient prime has its canonical Bezout inverse at every point of the fibre.
This supplies the invertibility instances required by the recorded coefficient stages,
using only the global convention l ≠ p.
Source: blueprint main-20261015, order 2415, coefficient convention
(blueprint: def-trf-scheme-frobenius). -/
@[instance_reducible]
noncomputable def schemeFrobeniusCoefficientInvertible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
  fun x ↦
    let ev := ((D.geometricFiber X₀).left.Γevaluation x).hom
    let f := pullback.fst X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom
    letI : CharP ((D.geometricFiber X₀).left.residueField x) D.p :=
      (CharP.charP_iff_prime_eq_zero D.prime).2
        ((map_natCast ev D.p).symm.trans
          ((congrArg ev (D.model_characteristic f)).trans (map_zero ev)))
    invertibleOfCoprime ((Nat.coprime_primes (Fact.out : l.Prime) D.prime).2 hl)

/-- Finite coefficient pullback along the m-th scheme Frobenius.
Uses the finite operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def schemeFrobeniusFiniteDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  finiteDerivedPullback l E n (D.schemeFrobeniusIterate X₀ m)

/-- Integral coefficient pullback along the m-th scheme Frobenius.
Uses the integral operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def schemeFrobeniusIntegralDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  constructibleIntegralPullback l E (D.schemeFrobeniusIterate X₀ m)

/-- Rational coefficient pullback along the m-th scheme Frobenius.
Uses the rational operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def schemeFrobeniusRationalDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  rationalDerivedPullback l E (D.schemeFrobeniusIterate X₀ m)

/-- CommonStage coefficient pullback along the m-th scheme Frobenius.
Uses the commonstage operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def schemeFrobeniusCommonStageDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  commonStageDerivedPullback l Ω (D.schemeFrobeniusIterate X₀ m)

/-- Finite coefficient pullback along the m-th geometric Galois Frobenius.
Uses the finite operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def geometricGaloisFiniteDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  finiteDerivedPullback l E n (((D.geometricFrobenius X₀) ^ m).hom)

/-- Integral coefficient pullback along the m-th geometric Galois Frobenius.
Uses the integral operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def geometricGaloisIntegralDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  constructibleIntegralPullback l E (((D.geometricFrobenius X₀) ^ m).hom)

/-- Rational coefficient pullback along the m-th geometric Galois Frobenius.
Uses the rational operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def geometricGaloisRationalDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  rationalDerivedPullback l E (((D.geometricFrobenius X₀) ^ m).hom)

/-- CommonStage coefficient pullback along the m-th geometric Galois Frobenius.
Uses the commonstage operation of `def-weil-derived-pullback-tensor-hom` unchanged.
Source: blueprint main-20261015, order 2415
(blueprint: def-trf-scheme-frobenius). -/
noncomputable def geometricGaloisCommonStageDerivedPullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (m : ℕ) :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  commonStageDerivedPullback l Ω (((D.geometricFrobenius X₀) ^ m).hom)

end WeilConjectures.FiniteFieldDatum
