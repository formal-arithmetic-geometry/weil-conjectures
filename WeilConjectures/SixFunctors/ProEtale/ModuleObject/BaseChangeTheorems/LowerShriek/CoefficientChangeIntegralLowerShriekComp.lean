/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIntegralComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral

/-!
# The composition of lower shrieks and the extension of scalars `𝒪_E ⟶ E`

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`.
This file shows that the composition isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the bounded
constructible `𝒪_E`- and `E`-sheaves are compatible with the extension of scalars `𝒪_E ⟶ E`
(`ProEtale.CondensedRing.squareCompatible_lowerShriekComp_extendScalars`): each step of their
construction (independence of the compactification, refinement, composition of extensions by
zero and of pushforwards, exchange of a pushforward and an extension by zero) is.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Composition

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

/-- The composition isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of `𝒪̲_E` and `E̲` are compatible with
the extension of scalars. -/
theorem squareCompatible_lowerShriekComp_extendScalars (f : X ⟶ Y) (g : Y ⟶ S) :
    NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
        (compactificationOverField (f ≫ g)))
      (Functor.pasteSquareIso
        ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
          (compactificationOverField f))
        ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
          (compactificationOverField g)))
      (boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g).hom
      (boundedConstructibleLowerShriekComp ℓ E f g).hom := by
  have hd := Compactification.exists_isPullback_overG_overI (compactificationOverField f)
    (compactificationOverField g)
  have : IsOpenImmersion ((compactificationOverField f).overI ≫ hd.choose.overI).left :=
    inferInstanceAs
      (IsOpenImmersion ((compactificationOverField f).overI.left ≫ hd.choose.overI.left))
  have : IsProper (Compactification.overCompObjIso (compactificationOverField f)
      (compactificationOverField g) hd.choose).hom.left := by
    simp only [Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have : IsProper (hd.choose.overG ≫ (compactificationOverField g).overG).left :=
    inferInstanceAs (IsProper (hd.choose.overG.left ≫ (compactificationOverField g).overG.left))
  have sqe : IsPullback (𝟙 X) ((compactificationOverField f).overComp
      (compactificationOverField g) hd.choose).overI
      ((compactificationOverField f).overI ≫ hd.choose.overI)
      (Compactification.overCompObjIso (compactificationOverField f)
        (compactificationOverField g) hd.choose).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers
    ℓ E.1 sqe
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sqe
  have := isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E.1 sqe
  have := isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers ℓ E.1
    hd.choose_spec
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E hd.choose_spec
  unfold boundedConstructibleLowerShriekComp_padicIntegers boundedConstructibleLowerShriekComp
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    asIso_inv]
  have s₂ : NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
        ((compactificationOverField f).overComp (compactificationOverField g) hd.choose))
      (Functor.pasteSquareIso
        ((extendScalarsCoefficientChange ℓ E k).shriek
          ((compactificationOverField f).overI ≫ hd.choose.overI))
        ((extendScalarsCoefficientChange ℓ E k).push
          (hd.choose.overG ≫ (compactificationOverField g).overG)))
      (PadicIntegersRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E.1 sqe
        (Compactification.overCompObjIso_hom_overG _ _ _)).inv
      (ContinuousMapRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E sqe
        (Compactification.overCompObjIso_hom_overG _ _ _)).inv :=
    ((extendScalarsCoefficientChange ℓ E k).squareCompatible_lowerShriekRefinementIso sqe
      (Compactification.overCompObjIso_hom_overG _ _ _)).inv
  have s₃ := NatTrans.SquareCompatible.whiskerRight
    ((extendScalarsCoefficientChange ℓ E k).push
      (hd.choose.overG ≫ (compactificationOverField g).overG))
    ((extendScalarsCoefficientChange ℓ E k).squareCompatible_openImmersionLowerShriekComp
      (compactificationOverField f).overI hd.choose.overI)
  have s₄ := NatTrans.SquareCompatible.whiskerLeft
    (Functor.pasteSquareIso
      ((extendScalarsCoefficientChange ℓ E k).shriek (compactificationOverField f).overI)
      ((extendScalarsCoefficientChange ℓ E k).shriek hd.choose.overI))
    ((extendScalarsCoefficientChange ℓ E k).squareCompatible_lowerStarComp
      (h := hd.choose.overG) (p := (compactificationOverField g).overG)).inv
  have s₅ := NatTrans.SquareCompatible.associator_hom
    ((extendScalarsCoefficientChange ℓ E k).shriek (compactificationOverField f).overI)
    ((extendScalarsCoefficientChange ℓ E k).shriek hd.choose.overI)
    (Functor.pasteSquareIso ((extendScalarsCoefficientChange ℓ E k).push hd.choose.overG)
      ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField g).overG))
  have s₆ := NatTrans.SquareCompatible.whiskerLeft
    ((extendScalarsCoefficientChange ℓ E k).shriek (compactificationOverField f).overI)
    ((NatTrans.SquareCompatible.associator_inv
      ((extendScalarsCoefficientChange ℓ E k).shriek hd.choose.overI)
      ((extendScalarsCoefficientChange ℓ E k).push hd.choose.overG)
      ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField g).overG)).comp
    ((NatTrans.SquareCompatible.whiskerRight
      ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField g).overG)
      (squareCompatible_lowerStarOpenImmersionLowerShriekExchange_extendScalars ℓ E
        hd.choose_spec).isIso_inv).comp
    (NatTrans.SquareCompatible.associator_hom
      ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField f).overG)
      ((extendScalarsCoefficientChange ℓ E k).shriek (compactificationOverField g).overI)
      ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField g).overG))))
  have s₇ := NatTrans.SquareCompatible.associator_inv
    ((extendScalarsCoefficientChange ℓ E k).shriek (compactificationOverField f).overI)
    ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField f).overG)
    (Functor.pasteSquareIso
      ((extendScalarsCoefficientChange ℓ E k).shriek (compactificationOverField g).overI)
      ((extendScalarsCoefficientChange ℓ E k).push (compactificationOverField g).overG))
  have s₁ := squareCompatible_lowerShriekOfCompactificationIso_extendScalars ℓ E (k := k)
    (compactificationOverField (f ≫ g))
    ((compactificationOverField f).overComp (compactificationOverField g) hd.choose)
  have s := s₁.comp (s₂.comp (s₃.comp (s₄.comp (s₅.comp (s₆.comp s₇)))))
  dsimp only [BoundedConstructibleCoefficientChange.shriekOfCompactification,
    padicIntegersPushforwardData_lowerStar, continuousMapPushforwardData_lowerStar,
    padicIntegersPushforwardData_lowerStarComp, continuousMapPushforwardData_lowerStarComp] at s ⊢
  exact s

end Composition

end AlgebraicGeometry.ProEtale.CondensedRing
