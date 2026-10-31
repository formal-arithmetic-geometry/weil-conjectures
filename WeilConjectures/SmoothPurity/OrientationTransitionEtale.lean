/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationTransitionTateSquare

/-!
# The finite orientations under the reduction of coefficients, on the étale site

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type which is smooth of pure
relative dimension `d`, and `Ψ` the derived extension of scalars along
`Λ = 𝒪_E ⧸ ℓⁿ⁺² ⟶ Λ' = 𝒪_E ⧸ ℓⁿ⁺¹`. The canonical finite orientation
`θₘ : red_m(𝒪(d))[2d] ≅ red_m(Rf^! 𝒪)` (`ProEtale.CondensedRing.etaleReductionSmoothOrientationIso`)
is assembled from three constituents: the reduction of the Tate twist, the diagonal orientation
`ω_f ≅ Λ_X(d)[2d]` (`Etale.dualizingComplexTwistShiftIso`) and the reduction of `Rf^! 𝒪`. This
file proves that `Ψ θₙ₊₂` is `θₙ₊₁` through the isomorphisms `β : Ψ(red_{n+2} -) ≅ red_{n+1} -`
(`ProEtale.CondensedRing.map_etaleReductionSmoothOrientationIso_hom_comp`), from the
compatibility of each constituent:

* the reduction of `Rf^! 𝒪`:
  `ProEtale.CondensedRing.map_etaleReductionUpperShriekUnitIso_hom_comp_dualizingComplexMap`;
* the diagonal orientation: `Etale.map_dualizingComplexTwistShiftIso_reduction_canonical`, for
  the canonical Tate data `Etale.reductionTateTwistShiftData`; its hypotheses are
  `Etale.reductionTateTwistShiftData_preservesKummerBoundaries` (frame classes) and
  `Etale.reductionTateTwistShiftData_preservesSectionInvariantIso`;
* the Tate twist: `ProEtale.CondensedRing.map_etaleReductionIntegralTateTwistIso_comp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The canonical finite orientations `θₙ : red_n(𝒪(d))[2d] ≅ red_n(Rf^! 𝒪)` are compatible with the
reduction of coefficients**: `Ψ θₙ₊₂` is `θₙ₊₁` through `β` and the commutation of `Ψ` with the
shift. -/
theorem map_etaleReductionSmoothOrientationIso_hom_comp (n : ℕ) :
    (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1 + 1)).hom ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom =
    ((integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).commShiftIso (2 * d : ℤ)).hom.app _ ≫
      (etaleReductionExtendScalarsIsoApp ℓ E.1 (n + 1) X _).hom⟦(2 * d : ℤ)⟧' ≫
        (etaleReductionSmoothOrientationIso ℓ E f d (n + 1)).hom := by
  have := HasCompactification.of_over f
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) X.left :=
    HasInvertibleExponent.of_hom X.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) X.left :=
    HasInvertibleExponent.of_hom X.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1)) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1)) Y.left :=
    HasInvertibleExponent.of_hom Y.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
      (pullback f.left f.left) := HasInvertibleExponent.of_hom (pullback.fst f.left f.left)
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E.1 (n + 1))
      (pullback f.left f.left) := HasInvertibleExponent.of_hom (pullback.fst f.left f.left)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : QuasiCompact f.left := HasCompactification.quasiCompact_of_locallyOfFiniteType f.left Y.hom
  have := Etale.isIso_derivedExtendScalarsLowerShriekMap_of_locallyOfFiniteType
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left Y.hom
  have := Etale.isIso_derivedExtendScalarsLowerShriekMap_of_locallyOfFiniteType
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) (pullback.fst f.left f.left) X.hom
  have hframe := fun (F : (pullback.diagonal f.left).EtaleFrame d) (_ : IsOpenImmersion F.e) ↦
    (Etale.reductionTateTwistShiftData_preservesKummerBoundaries
      (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
      (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
      (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1))).mapSupportedClass_frameClass F
  -- `hL` and `hD` are stated with the canonical Tate data spelled out rather than with the
  -- abbreviations `integersModPowTateShiftData` and `integersModPowSupportedCoefficientChange`:
  -- unifying the two spellings at default transparency is very slow, while `hD` is converted
  -- to the hypothesis of `map_etaleReductionSmoothOrientationIso_hom_comp_of` at reducible
  -- transparency
  have hL : (Etale.reductionSupportedCoefficientChange
        (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
        (ker_integersModPowCoeffTransition ℓ E.1 (n + 1))
        (Etale.reductionTateTwistShiftData (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
          (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
          (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1)))).PreservesSectionInvariantIso
      (pullback.diagonal f.left) := Etale.reductionTateTwistShiftData_preservesSectionInvariantIso
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
    (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1)) (pullback.diagonal f.left)
  have := Etale.isIso_derivedExtendScalarsRightDerivedUpperShriekMap_app
    (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
    (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left (integersModPowTateShiftData ℓ E n)
    d Y.hom hframe
  have hD := Etale.map_dualizingComplexTwistShiftIso_reduction_canonical
      (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
      (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left
      (Etale.reductionTateTwistShiftData (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
          (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) ℓ
          (ringChar_integersModPowCoeff_succ ℓ E.1 (n + 1)))
      d Y.hom hframe hL
  have hD' : (integersModPowDerivedExtendScalars ℓ E.1 (n + 1) X.left).map
          (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1 + 1))
            f.left d Y.hom).hom ≫
        ((integersModPowSupportedCoefficientChange ℓ E n).twistShiftConstantComplexIso
          X.left d).hom =
      Etale.derivedExtendScalarsDualizingComplexMap
          (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
          (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left
          (Etale.derivedExtendScalarsConstantComplexIso
            (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
            (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) Y.left) ≫
        (Etale.dualizingComplexTwistShiftIso (integersModPowCoeff.{u} ℓ E.1 (n + 1))
            f.left d Y.hom).hom := by
    with_reducible exact hD
  exact map_etaleReductionSmoothOrientationIso_hom_comp_of ℓ E f d n
    ((integersModPowSupportedCoefficientChange ℓ E n).twistShiftConstantComplexIso X.left d)
    (Etale.derivedExtendScalarsDualizingComplexMap
      (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
      (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) f.left
      (Etale.derivedExtendScalarsConstantComplexIso
        (integersModPowCoeffTransition_surjective ℓ E.1 (n + 1))
        (ker_integersModPowCoeffTransition ℓ E.1 (n + 1)) Y.left))
    (map_etaleReductionIntegralTateTwistIso_comp ℓ E d n) hD'
    (map_etaleReductionUpperShriekUnitIso_hom_comp_dualizingComplexMap ℓ E.1 (n + 1) f
      (map_etaleReductionUnitIso_hom_comp_constantComplexIso ℓ E.1 (n + 1) Y))

end AlgebraicGeometry.ProEtale.CondensedRing
