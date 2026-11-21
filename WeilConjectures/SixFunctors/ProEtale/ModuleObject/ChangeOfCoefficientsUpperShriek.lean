/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralToPadicAlgClUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLowerShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical

/-!
# Change of coefficients for the exceptional inverse image

Let `ℓ` be a prime, `k` a field of characteristic `p ≠ ℓ` and `f : X ⟶ Y` a morphism of separated
`k`-schemes of finite type. For a map of coefficient rings `Λ ⟶ Λ'` with extension of scalars
`T`, the exchange `β : Rf^!_Λ ⋙ T ⟶ T ⋙ Rf^!_{Λ'}` is the mate of the inverse of the coefficient
comparison for `Rf_!` under the adjunctions `Rf_! ⊣ Rf^!`. This file collects in a single
statement (`ProEtale.CondensedRing.isIso_upperShriekExchange_coefficientChange`) the coefficient
maps for which `β` is known to be an isomorphism on bounded constructible complexes:

* the reductions `Λ ⟶ Λ ⧸ J` of finite coefficient rings, on the étale site;
* the reductions `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`;
* the inclusions `E ⟶ F` of finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`;
* the inclusions `𝒪_E ⟶ E`, `E ⟶ ℚ̄_ℓ`, and their composite `𝒪_E ⟶ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Change of coefficients for the exceptional inverse image.** For a morphism `f : X ⟶ Y` of
separated `k`-schemes of finite type, the exchange `Rf^!_Λ ⋙ T ⟶ T ⋙ Rf^!_{Λ'}` for the
extension of scalars `T` along `Λ ⟶ Λ'` is an isomorphism on bounded constructible complexes
when `Λ ⟶ Λ'` is
1. the reduction `Λ ⟶ Λ ⧸ J` of a finite coefficient ring,
2. the reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
3. the inclusion `E ⟶ F` of finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`,
4. the inclusion `𝒪_E ⟶ E`,
5. the inclusion `E ⟶ ℚ̄_ℓ`,
6. the composite `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`. -/
theorem isIso_upperShriekExchange_coefficientChange (f : X ⟶ Y)
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (n : ℕ) :
    have := HasCompactification.of_over f
    (∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))]
      (J : Ideal Λ) (L : _root_.DerivedCategory
        (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y.left L →
        Nonempty ((Etale.reductionModIdeal Λ X.left J).obj
            ((Etale.rightDerivedUpperShriek Λ f.left).obj L) ≅
          (Etale.rightDerivedUpperShriek Λ f.left).obj
            ((Etale.reductionModIdeal Λ Y.left J).obj L))) ∧
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfCompactification ℓ E.1 n
        (compactificationOverField f)).inv)) ∧
    IsIso (boundedConstructibleUpperShriekExtendScalarsSubfield ℓ h f) ∧
    IsIso (boundedConstructibleUpperShriekExtendScalars ℓ E f) ∧
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) ∧
    IsIso (boundedConstructibleUpperShriekIntegersToPadicAlgCl ℓ E f) :=
  have := HasCompactification.of_over f
  ⟨fun Λ _ _ _ J _ hL ↦ Etale.nonempty_iso_reductionModIdeal_rightDerivedUpperShriek Λ J X.hom
      Y.hom f.left (Over.w f) hL,
    isIso_mateEquiv_etaleReductionLowerShriekIsoOfCompactification ℓ E.1 n _,
    isIso_boundedConstructibleUpperShriekExtendScalarsSubfield ℓ h f,
    isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f,
    isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E f,
    isIso_boundedConstructibleUpperShriekIntegersToPadicAlgCl ℓ E f⟩

end AlgebraicGeometry.ProEtale.CondensedRing
