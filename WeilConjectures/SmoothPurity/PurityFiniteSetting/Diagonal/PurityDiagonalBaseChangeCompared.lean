/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-!
# The specified diagonal base-change comparison in finite coordinates

Source: blueprint lem-pur-diagonal-base-change, all displayed comparisons
(blueprint: lem-pur-diagonal-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The diagonal chain, in its canonical etale presentation. Its first arrow is the
pullback of the inverse of the specified base-change mate, not an arbitrary isomorphism.
Source: blueprint lem-pur-diagonal-base-change, final chain
(blueprint: lem-pur-diagonal-base-change). -/
def finiteDiagonalRestriction (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (b : (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ f) ≅
      Etale.dualizingComplex Λ (pullback.fst f f)) :
    Etale.sectionInvariant Λ (pullback.fst f f) (pullback.diagonal f) ≅
      Etale.dualizingComplex Λ f :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _

/-- The diagonal chain, in its canonical etale presentation. Its first arrow is the
pullback of the inverse of the specified base-change mate, not an arbitrary isomorphism.
Source: blueprint lem-pur-diagonal-base-change, final chain
(blueprint: lem-pur-diagonal-base-change). -/
def diagonalComparedRestriction (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex P.Coefficient f) ≅
      Etale.dualizingComplex P.Coefficient (pullback.fst f f)) :
    Etale.sectionInvariant P.Coefficient (pullback.fst f f) (pullback.diagonal f) ≅
      Etale.dualizingComplex P.Coefficient f :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _

/-- Both self-product base-change mates are invertible; the displayed restriction
construction then supplies exactly the specified diagonal comparison.
Source: blueprint lem-pur-diagonal-base-change, all three chains
(blueprint: lem-pur-diagonal-base-change).
Proof: the fibre-product universal property gives the two Cartesian squares and the
section identities. Smooth base change of thm-pur-cohomological-smoothness clause 3
makes each specified counit mate invertible. The coefficient exponent is invertible
because the fixed coefficient prime differs from the characteristic. Pull the inverse
of the first mate along the diagonal, compose pullbacks, and use diagonal_snd and
identity pullback. These are precisely diagonalComparedRestriction and its explicit
comparison-site transport diagonalComparedProEtale. No orientation is involved. -/
theorem comparedDiagonalBaseChange (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] [SmoothOfRelativeDimension d f]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hf : f ≫ aY = aX) :
    IsPullback (pullback.snd f f) (pullback.fst f f) f f ∧
    SmoothOfRelativeDimension d (pullback.fst f f) ∧
    SmoothOfRelativeDimension d (pullback.snd f f) ∧
    IsIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f).flip) ∧
    IsIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f)) := by
  have _ := hf
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : HasInvertibleExponent P.Coefficient X := by
    let l := P.coefficients.l
    let E := P.extension
    let n := P.level
    have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
    have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      calc
        Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
          change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
          simpa only [map_natCast] using
            (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
        _ < 1 := Padic.norm_p_lt_one
    have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
        Padic.coefficientExtensionMaximalIdeal l E :=
      (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
        Padic.coefficientExtensionIdeal l E n := by
      change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ n
      rw [hgen]
      exact Ideal.pow_mem_pow hlm n
    refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
    · apply ULift.ext
      change ((l ^ n : ℕ) : Padic.coefficientExtensionIntegers l E ⧸
        Padic.coefficientExtensionIdeal l E n) = 0
      rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
        Ideal.Quotient.eq_zero_iff_mem]
      simpa only [Nat.cast_pow] using hpow
    · apply X.toRingedSpace.isUnit_of_isUnit_germ
      intro x hx
      change IsUnit ((X.toRingedSpace.presheaf.germ ⊤ x hx).hom
        ((l ^ n : ℕ) : X.toRingedSpace.presheaf.obj _))
      rw [map_natCast, Nat.cast_pow]
      exact (P.coefficientPrime_isUnit_stalk X aX x).pow n
  refine ⟨(IsPullback.of_hasPullback f f).flip, inferInstance, inferInstance, ?_, ?_⟩
  · have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      P.Coefficient f d (IsPullback.of_hasPullback f f).flip
    exact (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient
      (IsPullback.of_hasPullback f f).flip).2 inferInstance
  · have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      P.Coefficient f d (IsPullback.of_hasPullback f f)
    exact (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient
      (IsPullback.of_hasPullback f f)).2 inferInstance

end WeilConjectures.PurityFiniteSetting
