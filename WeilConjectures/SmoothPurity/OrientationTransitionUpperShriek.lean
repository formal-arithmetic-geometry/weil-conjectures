/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonical
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical

/-!
# The reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` and the exceptional functors

Write `Ψ` for the derived extension of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site and
`β : Ψ(red_{n+1} K) ≅ red_n K` for its compatibility with the reductions
(`ProEtale.CondensedRing.etaleReductionExtendScalarsIsoApp`). For a morphism `f : X ⟶ Y` of
separated `k`-schemes of finite type, this file (blueprint `det-sp-purity-coefficient-change`)

* states the compatibility of `β` with the canonical comparisons
  `Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!` (`etaleReductionLowerShriekIsoOfCompactification`) and the
  comparison `β_f : Ψ Rf_! ⟶ Rf_! Ψ` (`Etale.derivedExtendScalarsLowerShriekMap`):
  `map_etaleReductionLowerShriekIso_hom_comp_derivedExtendScalarsLowerShriekMap`;
* deduces, by passing to the mates, the compatibility of `β` with the canonical comparisons
  `Rf^! ⋙ red_X ≅ red_Y ⋙ Rf^!` (`etaleReductionUpperShriekIso`) and the comparison
  `c_f : Ψ Rf^! ⟶ Rf^! Ψ`:
  `map_etaleReductionUpperShriekIso_hom_app_comp_upperShriekMap`;
* deduces the compatibility of `β` with the identification `red_X(Rf^! 𝒪) ≅ Rf^! Λ` and the
  comparison `Ψ ω_f ⟶ ω'_f` of the dualizing complexes, given the one with the units:
  `map_etaleReductionUpperShriekUnitIso_hom_comp_dualizingComplexMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [HasCompactification f.left] [CompactSpace Y.left]

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The reduction `β` is compatible with the comparisons for `Rf_!`**: through
`β : Ψ(red_{n+1} -) ≅ red_n -`, the derived extension of scalars `Ψ` of the canonical comparison
`Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!` modulo `ℓⁿ⁺¹` (`etaleReductionLowerShriekIsoOfCompactification`, for
the chosen compactification `compactificationOverField f`), followed by the comparison
`β_f : Ψ Rf_! ⟶ Rf_! Ψ` (`Etale.derivedExtendScalarsLowerShriekMap`), is the canonical comparison
modulo `ℓⁿ`. -/
theorem map_etaleReductionLowerShriekIso_hom_comp_derivedExtendScalarsLowerShriekMap
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (integersModPowDerivedExtendScalars ℓ E n Y.left).map
        ((etaleReductionLowerShriekIsoOfCompactification ℓ E (n + 1)
          (compactificationOverField f)).hom.app K) ≫
      (Etale.derivedExtendScalarsLowerShriekMap (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) f.left).app
          ((etaleReduction ℓ E (n + 1) X).obj K) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        f.left).map (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom =
    (etaleReductionExtendScalarsIsoApp ℓ E n Y
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f).obj K)).hom ≫
      (etaleReductionLowerShriekIsoOfCompactification ℓ E n
        (compactificationOverField f)).hom.app K := by
  exact reductionSquareCompatible_etaleReductionLowerShriekIsoOfCompactification ℓ E n
    (compactificationOverField f) K

omit [HasCompactification f.left] [CompactSpace Y.left] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] in
/-- The components of `etaleReductionExtendScalarsIso`, written with
`etaleReductionExtendScalarsIsoApp`. -/
lemma etaleReductionExtendScalarsIso_hom_app_eq {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (K : Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReductionExtendScalarsIso ℓ E n Z).hom.app K =
      (etaleReductionExtendScalarsIsoApp ℓ E n Z K).hom :=
  rfl

variable [IsIso (Etale.derivedExtendScalarsLowerShriekMap
  (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
  f.left)]

set_option maxRecDepth 4000 in
-- unfolding the mates of the comparison squares is deep
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The reduction `β` is compatible with the comparisons for `Rf^!`**: through
`β : Ψ(red_{n+1} -) ≅ red_n -`, the derived extension of scalars `Ψ` of the canonical comparison
`Rf^! ⋙ red_X ≅ red_Y ⋙ Rf^!` modulo `ℓⁿ⁺¹` (`etaleReductionUpperShriekIso`), followed by the
comparison `c_f : Ψ Rf^! ⟶ Rf^! Ψ` (`Etale.derivedExtendScalarsRightDerivedUpperShriekMap`), is the
canonical comparison modulo `ℓⁿ`. Both comparisons are mates of comparisons for `Rf_!`, which are
compatible (`map_etaleReductionLowerShriekIso_hom_comp_derivedExtendScalarsLowerShriekMap`). -/
theorem map_etaleReductionUpperShriekIso_hom_app_comp_upperShriekMap
    (N : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (integersModPowDerivedExtendScalars ℓ E n X.left).map
        ((etaleReductionUpperShriekIso ℓ E (n + 1) f).hom.app N) ≫
      (Etale.derivedExtendScalarsRightDerivedUpperShriekMap
        (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
          f.left).app ((etaleReduction ℓ E (n + 1) Y).obj N) ≫
      (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) f.left).map
        (etaleReductionExtendScalarsIsoApp ℓ E n Y N).hom =
    (etaleReductionExtendScalarsIsoApp ℓ E n X
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj N)).hom ≫
      (etaleReductionUpperShriekIso ℓ E n f).hom.app N := by
  have h := map_mateEquiv_app_comp_mateEquiv_app_comp_map_eq
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (etaleReductionLowerShriekIsoOfCompactification ℓ E (n + 1) (compactificationOverField f))
    (etaleReductionLowerShriekIsoOfCompactification ℓ E n (compactificationOverField f))
    (Etale.derivedExtendScalarsLowerShriekMap (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) f.left)
    (etaleReductionExtendScalarsIso ℓ E n X) (etaleReductionExtendScalarsIso ℓ E n Y)
    (fun K ↦ by
      rw [etaleReductionExtendScalarsIso_hom_app_eq, etaleReductionExtendScalarsIso_hom_app_eq]
      exact map_etaleReductionLowerShriekIso_hom_comp_derivedExtendScalarsLowerShriekMap ℓ E n f
        K) N
  rw [etaleReductionExtendScalarsIso_hom_app_eq, etaleReductionExtendScalarsIso_hom_app_eq] at h
  rw [etaleReductionUpperShriekIso_hom, etaleReductionUpperShriekIso_hom]
  exact h

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The reduction `β` is compatible with the identifications `red(Rf^! 𝒪) ≅ Rf^! Λ`**: through
`β`, the derived extension of scalars of `red_X(Rf^! 𝒪) ≅ Rf^!(red_Y 𝒪) ≅ Rf^! Λ` modulo `ℓⁿ⁺¹`
(`etaleReductionUpperShriekIso`, `etaleReductionUnitIso`), followed by the comparison
`Ψ ω_f ⟶ ω'_f` of the dualizing complexes (`Etale.derivedExtendScalarsDualizingComplexMap`), is the
identification modulo `ℓⁿ`, as soon as `β` is compatible with the identifications
`red_Y 𝒪 ≅ Λ` and `Ψ Λ ≅ Λ'` of the units (`hb`). -/
theorem map_etaleReductionUpperShriekUnitIso_hom_comp_dualizingComplexMap
    (hb : (integersModPowDerivedExtendScalars ℓ E n Y.left).map
          (etaleReductionUnitIso ℓ E (n + 1) Y).hom ≫
        (Etale.derivedExtendScalarsConstantComplexIso
          (integersModPowCoeffTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom =
      (etaleReductionExtendScalarsIsoApp ℓ E n Y (𝟙_ _)).hom ≫
        (etaleReductionUnitIso ℓ E n Y).hom) :
    (integersModPowDerivedExtendScalars ℓ E n X.left).map
        ((etaleReductionUpperShriekIso ℓ E (n + 1) f).app (𝟙_ _) ≪≫
          (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E (n + 1))
            f.left).mapIso (etaleReductionUnitIso ℓ E (n + 1) Y)).hom ≫
      Etale.derivedExtendScalarsDualizingComplexMap
        (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
        f.left (Etale.derivedExtendScalarsConstantComplexIso
          (integersModPowCoeffTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n) Y.left) =
    (etaleReductionExtendScalarsIsoApp ℓ E n X _).hom ≫
      ((etaleReductionUpperShriekIso ℓ E n f).app (𝟙_ _) ≪≫
        (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) f.left).mapIso
          (etaleReductionUnitIso ℓ E n Y)).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Etale.derivedExtendScalarsDualizingComplexMap_eq]
  exact map_comp_map_app_comp_map_eq _ _ _ _ _ _ _ _
    (map_etaleReductionUpperShriekIso_hom_app_comp_upperShriekMap
      ℓ E n f (𝟙_ _)) hb

end AlgebraicGeometry.ProEtale.CondensedRing
