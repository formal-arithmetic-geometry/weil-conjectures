/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalizationUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekIso

/-!
# The reduction of the integral dualizing complex

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). This file proves that `red_X` carries the
integral dualizing complex `ω_{X, 𝒪_E} = Ra_X^! 𝒪_E` to the étale dualizing complex
`ω_X = Ra_X^! (𝒪_E ⧸ ℓⁿ)` (blueprint `det-pd-biduality-coefficients`, proof of (ii), from the
coefficient comparison for `f^!` of blueprint `det-prop-scalar-six-exceptional`).

The structure morphism `a_X` factors through a compactification as an open immersion `j`
followed by a proper `p`; the reduction commutes with `Rp^!` (`exists_etaleReductionLowerShriekIso`)
and with `Rj^! = j^*` (`nonempty_etaleReductionUpperStarIso`), and it sends the unit `𝒪_E` to the
unit (`etaleReductionUnitIso`).

## Main definitions

- `ProEtale.CondensedRing.etaleReductionDualizingComplexIso`:
  `red_X ω_{X, 𝒪_E} ≅ ω_X`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- Reduction modulo `ℓⁿ` commutes with the exceptional inverse image along a proper `p`, in the
form `Rp^! = (Rp_*)^ʳ` (the chosen right adjoint of the pushforward, which enters
`PadicIntegersRingObj.boundedConstructibleUpperShriekOfCompactification`): it is the
right adjoint of `Rp_! ≅ Rp_*` (`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`), and
the transpose of the comparison of `exists_etaleReductionLowerShriekIso` is invertible. -/
noncomputable def etaleReductionProperUpperShriekIso {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    haveI := HasCompactification.of_over p
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p).rightAdjoint ⋙
        etaleReduction ℓ E n Z ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) p.left :=
  haveI := HasCompactification.of_over p
  haveI := (exists_etaleReductionLowerShriekIso ℓ E n p).choose_spec
  Functor.isoWhiskerRight ((Adjunction.ofIsLeftAdjoint _).rightAdjointUniq
    ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p).ofNatIsoLeft
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p))) _ ≪≫
    asIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p)
      (Etale.rightDerivedUpperShriekAdjunction _ p.left)
      (TwoSquare.mk _ _ _ _ (exists_etaleReductionLowerShriekIso ℓ E n p).choose.inv))

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **The reduction of the integral dualizing complex is the étale dualizing complex**:
`red_X (Ra_X^! 𝒪_E) ≅ Ra_X^! (𝒪_E ⧸ ℓⁿ)` (blueprint `det-prop-scalar-six-exceptional` for
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site, at the unit).

For the chosen compactification `X ⟶[i] Z ⟶[p] Spec k` of `a_X`, `Ra_X^! 𝒪_E = i^* Rp^! 𝒪_E`;
the reduction commutes with `i^*` (`etaleReductionUpperStarIso`) and with `Rp^!`
(`etaleReductionProperUpperShriekIso`), sends the unit to the unit (`etaleReductionUnitIso`), and
`Li^* Rp^! ≅ R(i ≫ p)^!` on the étale side
(`Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`). -/
noncomputable def etaleReductionDualizingComplexIso :
    (etaleReduction ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E X) ≅
      Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E n) X.hom :=
  let c := compactificationOverField (Over.mkIdTerminal.from X)
  haveI := HasCompactification.of_over c.overG
  (etaleReductionUpperStarIso ℓ E n c.overI).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
      c.i).leftDerivedFunctor.mapIso
      ((etaleReductionProperUpperShriekIso ℓ E n c.overG).app (𝟙_ _) ≪≫
        (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) c.g).mapIso
          (etaleReductionUnitIso ℓ E n _)) ≪≫
    ((Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale
      (integersModPowCoeff.{u} ℓ E n) c.i c.g X.hom (by simpa using c.comm.symm)).some.app (𝟙_ _))

end AlgebraicGeometry.ProEtale.CondensedRing
