/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.OverProduct
public import Submission.WeilConjectures.Compactification.NagataCompactification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekMate

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- **Reduction comparisons compose**: if `f` and `g` have a reduction comparison for the
lower and upper shrieks, so does `f ≫ g`. The comparison for `f ≫ g` is the stacked square of
those for `f` and `g`, transported along the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`boundedConstructibleLowerShriekComp_padicIntegers` and
`Etale.nonempty_iso_rightDerivedLowerShriek_comp`); its transpose is invertible by
`CategoryTheory.isIso_mateEquiv_vComp_whiskerLeft_whiskerRight`. -/
theorem HasEtaleReductionLowerShriekIso.comp {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : HasEtaleReductionLowerShriekIso ℓ E n f)
    (hg : HasEtaleReductionLowerShriekIso ℓ E n g) :
    HasEtaleReductionLowerShriekIso ℓ E n (f ≫ g) := by
  have := HasCompactification.of_over f
  have := HasCompactification.of_over g
  have := HasCompactification.of_over (f ≫ g)
  obtain ⟨γf, hγf⟩ := hf
  obtain ⟨γg, hγg⟩ := hg
  obtain ⟨e'⟩ := Etale.nonempty_iso_rightDerivedLowerShriek_comp
    (integersModPowCoeff.{u} ℓ E n) f.left g.left
  let sqf := TwoSquare.mk _ _ _ _ γf.inv
  let sqg := TwoSquare.mk _ _ _ _ γg.inv
  let c := boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g
  let sq := ((sqf.vComp sqg).whiskerLeft c.inv).whiskerRight e'.hom
  have : IsIso sq.natTrans := by
    have : IsIso sqf.natTrans := inferInstanceAs (IsIso γf.inv)
    have : IsIso sqg.natTrans := inferInstanceAs (IsIso γg.inv)
    have := sqf.isIso_vComp sqg
    have := (sqf.vComp sqg).isIso_whiskerLeft c.inv
    exact ((sqf.vComp sqg).whiskerLeft c.inv).isIso_whiskerRight e'.hom
  refine ⟨(asIso sq.natTrans).symm, ?_⟩
  exact isIso_mateEquiv_vComp_whiskerLeft_whiskerRight
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (Etale.rightDerivedUpperShriekAdjunction _ f.left)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E g)
    (Etale.rightDerivedUpperShriekAdjunction _ g.left)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E (f ≫ g))
    (Etale.rightDerivedUpperShriekAdjunction _ (f ≫ g).left)
    (boundedConstructibleLowerShriekComp_padicIntegers ℓ E f g) e' _ _

/-! ### Factorization of proper morphisms -/

end AlgebraicGeometry.ProEtale.CondensedRing
