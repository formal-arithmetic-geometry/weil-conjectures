/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateOfNatIsoLeft
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.IntegralReductionUpperShriek

/-!
# The étale reduction `f^!` clause for proper morphisms, modulo finite-coefficient inputs

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). By definition it factors as
```
Dᵇc(X)⟦𝒪_E⟧ --red--> Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ --ρ_X--> D(X_ét, 𝒪_E ⧸ ℓⁿ),
```
the condensed reduction followed by the *étale reading* `ρ_X = Rν_* ∘ Φ` of bounded constructible
condensed `𝒪_E ⧸ ℓⁿ`-complexes (`ProEtale.CondensedRing.finiteEtaleReading`).

For a proper `p : X ⟶ Y`, this file proves that `p` has a reduction comparison for `Rp_!` and
`Rp^!` (`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso`) from:

1. the compatibilities of (Pull) for `p` with the natural reduction triangles
   (`ProEtale.CondensedRing.IntegersModPowPullUnitCompatible`,
   `ProEtale.CondensedRing.IntegersModPowPullδCompatible`);
2. restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` preserves bounded constructible complexes on
   `X` and `Y` (`ProEtale.CondensedRing.RestrictScalarsIntegersModPowBoundedConstructible`);
3. the **finite-coefficient comparison for `p^!`**
   (`ProEtale.CondensedRing.HasEtaleReadingUpperShriekComparison`): `Rp_*` on
   `Dᵇc(-)⟦𝒪_E ⧸ ℓⁿ⟧` has a right adjoint `H'`, and the étale reading commutes with the
   pushforwards through an isomorphism whose transpose `H' ⋙ ρ_X ⟶ ρ_Y ⋙ Rp^!` is invertible.
   No integral coefficients are involved: this is the statement that the étale reading
   identifies the condensed `𝒪_E ⧸ ℓⁿ`-six functors with the étale ones for `p^!`.

(`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_isProper_of_compatible`.) The
reduction comparison is the paste of the condensed comparison
(`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarIntegersModPowReduction`,
the formal reduction-triangle argument) with the finite-coefficient comparison of 3, after
replacing `Rp_!` by `Rp_*` (`CategoryTheory.mateEquiv_ofNatIsoLeft`); the mate of a paste is the
paste of the mates (`CategoryTheory.isIso_mateEquiv_hComp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **The étale reading of bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes**: `M ↦ Rν_* Φ(M)`, from
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes on `X_proét` to the derived category of
étale sheaves of `𝒪_E ⧸ ℓⁿ`-modules on `X`. The étale reduction `etaleReduction` is the
condensed reduction followed by it. -/
noncomputable def finiteEtaleReading (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      DerivedCategory (Sheaf Y.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  (boundedConstructible _).ι ⋙
    (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The finite-coefficient comparison for `p^!`** (proper `p`): the pushforward `Rp_*` on
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes has a right adjoint `H'`, and there is an
isomorphism `Rp_* ⋙ ρ_Y ≅ ρ_X ⋙ Rp_!` (`ρ = finiteEtaleReading`, `Rp_!` étale) whose transpose
`H' ⋙ ρ_X ⟶ ρ_Y ⋙ Rp^!` under `Rp_* ⊣ H'` and the étale `Rp_! ⊣ Rp^!` is an isomorphism. -/
def HasEtaleReadingUpperShriekComparison (p : X ⟶ Y) : Prop :=
  have := HasCompactification.of_over p
  ∃ (H' : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧)
    (adjH' : boundedConstructibleLowerStar (Profinite.integersModPowRingObj ℓ E n) ℓ p ⊣ H')
    (γ : boundedConstructibleLowerStar (Profinite.integersModPowRingObj ℓ E n) ℓ p ⋙
        finiteEtaleReading ℓ E n Y ≅
      finiteEtaleReading ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left),
    IsIso (mateEquiv adjH' (Etale.rightDerivedUpperShriekAdjunction _ p.left)
      (TwoSquare.mk _ _ _ _ γ.inv))

/-- **The étale reduction `f^!` clause for a proper morphism**, from the compatibilities of
(Pull) with the natural reduction triangles, the preservation of bounded constructible
complexes by restriction of scalars, and the finite-coefficient comparison for `p^!`. -/
theorem hasEtaleReductionLowerShriekIso_of_isProper_of_compatible (p : X ⟶ Y) [IsProper p.left]
    (hη : IntegersModPowPullUnitCompatible ℓ E n p.left)
    (hδ : IntegersModPowPullδCompatible ℓ E n p.left)
    (hX : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n X.left)
    (hY : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n Y.left)
    (hC : HasEtaleReadingUpperShriekComparison ℓ E n p) :
    HasEtaleReductionLowerShriekIso ℓ E n p := by
  have := HasCompactification.of_over p
  obtain ⟨H', adjH', γC, hγC⟩ := hC
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n p hη hδ
  let γB := asIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n p)
  have hB := isIso_mateEquiv_boundedConstructibleLowerStarIntegersModPowReduction p hX hY hη hδ
    adjH' γB rfl
  rw [mateEquiv_ofNatIsoLeft] at hB
  let α : TwoSquare (boundedConstructibleIntegersModPowReduction X.left ℓ E n)
      (boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ p)
      (boundedConstructibleLowerStar (Profinite.integersModPowRingObj ℓ E n) ℓ p)
      (boundedConstructibleIntegersModPowReduction Y.left ℓ E n) :=
    TwoSquare.mk _ _ _ _ (γB.inv ≫ Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p).inv _)
  let β : TwoSquare (finiteEtaleReading ℓ E n X)
      (boundedConstructibleLowerStar (Profinite.integersModPowRingObj ℓ E n) ℓ p)
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left)
      (finiteEtaleReading ℓ E n Y) :=
    TwoSquare.mk _ _ _ _ γC.inv
  have : IsIso α.natTrans := inferInstanceAs (IsIso (γB.inv ≫ _))
  have : IsIso β.natTrans := inferInstanceAs (IsIso γC.inv)
  have := TwoSquare.isIso_hComp α β
  have : IsIso (mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ p) adjH' α).natTrans :=
    hB
  have : IsIso (mateEquiv adjH' (Etale.rightDerivedUpperShriekAdjunction _ p.left) β).natTrans :=
    hγC
  refine ⟨(asIso (α.hComp β).natTrans).symm, ?_⟩
  exact isIso_mateEquiv_hComp (boundedConstructibleUpperShriekAdjunction _ ℓ p) adjH'
    (Etale.rightDerivedUpperShriekAdjunction _ p.left) α β

end AlgebraicGeometry.ProEtale.CondensedRing
