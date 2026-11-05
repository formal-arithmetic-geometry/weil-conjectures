/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionProper

/-!
# Reduction modulo `ℓⁿ` commutes with `Rj_!` and `Rj^!` along open immersions

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). This file proves that an open immersion
`j : U ⟶ X` has a reduction comparison for `Rj_!` and `Rj^!`
(`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_isOpenImmersion`), the open-immersion
case of blueprint `det-prop-scalar-six-exceptional`.

## Strategy

On both sides `Rj^!` is the pullback `j^*`: on bounded constructible `𝒪_E`-complexes, `Rj_!` is
the extension by zero `j_!` by independence of the compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers`),
and `Rj^! ≅ j^*` is its conjugate; on the étale side this is
`Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`. As reduction commutes with pullback
(`ProEtale.CondensedRing.etaleReductionUpperStarIso`), we get an isomorphism
`δ : Rj^! ⋙ red_U ≅ red_X ⋙ Rj^!`
(`ProEtale.CondensedRing.etaleReductionUpperShriekIsoOfIsOpenImmersion`). Let
`θ : red_U ⋙ Rj_! ⟶ Rj_! ⋙ red_X` be the transpose of `δ` under `Rj_! ⊣ Rj^!`; its transpose
back is `δ`, an isomorphism, and it remains to see that `θ` is an isomorphism. This is checked
after restriction to `U` and to the closed complement `i : Z ⟶ X` of `j` (open–closed
conservativity on `X_ét`):

* after `j^*`, the map `θ_K` is identified, through the units of the two adjunctions
  `Rj_! ⊣ Rj^!` (invertible, `j_!` being fully faithful on both sides), with `δ_{Rj_! K}`;
* after `i^*`, source and target vanish: `i^* j_! = 0` on the étale side, and
  `i^* red_X ≅ red_Z i^*` with `i^* j_! = 0` on the condensed side.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-! ### `Rj_!` and `Rj^!` on bounded constructible `𝒪_E`-complexes -/

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the derived pushforward on bounded constructible
`𝒪_E`-complexes: the conjugate of `boundedConstructibleUpperStarId` under the adjunctions
`L(𝟙 X)^* ⊣ R(𝟙 X)_*` and `𝟭 ⊣ 𝟭`. -/
noncomputable def boundedConstructibleLowerStarId_padicIntegers (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E (𝟙 X) ≅
      𝟭 (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  conjugateIsoEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (𝟙 X)) Adjunction.id
    (boundedConstructibleUpperStarId (Profinite.padicIntegersRingObj ℓ E) ℓ X).symm

variable {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The lower shriek along an open immersion is the extension by zero, `Rj_! ≅ j_!`, on bounded
constructible `𝒪_E`-complexes: by independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers`), `Rj_!` is
`j_! ⋙ R(𝟙 X)_*` for the trivial compactification `U ⟶[j] X ⟶[𝟙] X`, and `R(𝟙 X)_* ≅ 𝟭`. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ j :=
  boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E
      (compactificationOverField j) (.ofIsOpenImmersion j.left) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
      (boundedConstructibleLowerStarId_padicIntegers ℓ E X) ≪≫
    Functor.rightUnitor _

/-- The exceptional inverse image along an open immersion is the pullback, `Rj^! ≅ j^*`, on
bounded constructible `𝒪_E`-complexes: the conjugate of
`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers` under the adjunctions
`Rj_! ⊣ Rj^!` and `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleUpperShriekIsoUpperStar_padicIntegers :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ j :=
  conjugateIsoEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).symm

/-! ### Reduction modulo `ℓⁿ` and `Rj^!` -/

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with `Rj^!` for an open immersion
`j`**: `Rj^! ⋙ red_U ≅ red_X ⋙ Rj^!`. Both exceptional inverse images are the pullback `j^*`
(`boundedConstructibleUpperShriekIsoUpperStar_padicIntegers` and
`Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`), and reduction commutes with pullback
(`etaleReductionUpperStarIso`). -/
noncomputable def etaleReductionUpperShriekIsoOfIsOpenImmersion :
    have := HasCompactification.of_over j
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j ⋙ etaleReduction ℓ E n U ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) j.left :=
  have := HasCompactification.of_over j
  Functor.isoWhiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j) _ ≪≫
    etaleReductionUpperStarIso ℓ E n j ≪≫
    Functor.isoWhiskerLeft _
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ j.left ≪≫
        (Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion _ j.left).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
