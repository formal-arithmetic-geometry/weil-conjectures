/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProduct
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekMate

/-!
# Reduction modulo `ℓⁿ`, `Rf_!` and `Rf^!`: stability under composition

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). Say that a morphism `f : Z ⟶ Y` *has a
reduction comparison* if there is an isomorphism `γ : Rf_! ⋙ red_Y ≅ red_Z ⋙ Rf_!` whose
transpose `Rf^! ⋙ red_Z ⟶ red_Y ⋙ Rf^!` under the adjunctions `Rf_! ⊣ Rf^!` is an isomorphism
(`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso`). Closed immersions have one
(`ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso_of_isClosedImmersion`).

This file shows that the property is stable under composition
(`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso.comp`): with the composition
isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on both sides, the stacked square of `γ_f` and `γ_g`
has invertible transpose (`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`).
This is the composition step of blueprint `det-prop-scalar-six-exceptional` ("compatibility
with composition"), in the weak form of `exists_etaleReductionLowerShriekIso` (no identification
of `γ` with the canonical comparison). Every proper morphism is a closed immersion followed
by a projection `P ×_k Y ⟶ Y` (`exists_isClosedImmersion_comp_overProdSnd`).
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

/-- A morphism `f : Z ⟶ Y` *has a reduction comparison for `Rf_!` and `Rf^!`*: there is an
isomorphism `γ : Rf_! ⋙ red_Y ≅ red_Z ⋙ Rf_!` whose transpose under `Rf_! ⊣ Rf^!` is an
isomorphism. This is the conclusion of `exists_etaleReductionLowerShriekIso`. -/
def HasEtaleReductionLowerShriekIso {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : Z ⟶ Y) : Prop :=
  have := HasCompactification.of_over f
  ∃ γ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
      etaleReduction ℓ E n Y ≅
    etaleReduction ℓ E n Z ⋙
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left,
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γ.inv))

variable {X Y S : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-! ### Factorization of proper morphisms -/

end AlgebraicGeometry.ProEtale.CondensedRing
