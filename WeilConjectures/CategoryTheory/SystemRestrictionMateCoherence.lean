/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.SystemRestrictionMateCoherenceData
import WeilConjectures.CategoryTheory.SystemRestrictionMateCoherenceEquations

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-mate-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))


variable (HB : StrictRingSystem BX ⥤ StrictRingSystem BY) [HB.Additive]
  (HA : StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj AY)) [HA.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  (adjB : FB.functor ⊣ HB) (adjA : FA.functor ⊣ HA)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, FB.levelFunctor n ⊣ Hn n)
  (H0 : systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0 ⥤
    systemLevel ((Functor.const ℕᵒᵖ).obj AY) 0) [H0.Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)]
  (adj0 : FA.levelFunctor 0 ⊣ H0)

/-- Compatible scalar and transition squares have invertible derived direct-image
mates, and exact localization preserves their evaluation and transition coherence.

Source: Stacks Project, Tags 03D2, 03DA, 0D6E and 07A6
(blueprint: lem-route-system-restriction-mate-coherence).

Proof: Construct the ordinary normalization datum d with exactly the supplied level and
restriction fields: its scalar component is assembled levelwise from the evaluation
isomorphisms, the level comparison and the restriction/evaluation isomorphisms, and
commutes with transitions by faithfulness of the underlying-sheaf functor and the
transition equations of the two geometric inverse images. The invertibility of the
scalar, level and transition derived mates of this datum are the two separate
invertibility assertions (scalar restriction commutes with derived module direct image,
Stacks 0D6E). The scalar/evaluation identity follows by localizing the scalar cube and
applying the mate-cube theorem; the transition identity by transposing under the level
adjunction, using the mate/counit equations and the localized ordinary transition square
(SystemRestrictionMateCoherenceData, SystemRestrictionMateCoherenceEquations). -/
theorem systemRestrictionMateCoherence
    (htransition : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (IB n).ringUnderlying.hom =
        (IB m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (halgebra : ∀ n : ℕ,
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (aY.app (op n))) ≫ (IB n).ringUnderlying.hom =
        IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (aX.app (op n)))
    (level : ∀ n : ℕ,
    FB.levelFunctor n ⋙ singletonLevelRestriction aX n ≅
      singletonLevelRestriction aY n ⋙ FA.levelFunctor 0)
    (levelUnderlying : ∀ (n : ℕ) (M : systemLevel BY n),
    (systemGeometricUnderlying ((Functor.const ℕᵒᵖ).obj AX) 0).map
          ((level n).hom.app M) ≫
        IA.moduleUnderlying.hom.app ((singletonLevelRestriction aY n).obj M) =
      (IB n).moduleUnderlying.hom.app M)
    (restriction : ∀ {n m : ℕ} (h : n ≤ m),
    FB.levelFunctor n ⋙ systemRestriction BX h ≅
      systemRestriction BY h ⋙ FB.levelFunctor m)
    (restrictionUnderlying : ∀ {n m : ℕ} (h : n ≤ m) (M : systemLevel BY n),
    (systemGeometricUnderlying BX m).map ((restriction h).hom.app M) ≫
        (IB m).moduleUnderlying.hom.app ((systemRestriction BY h).obj M) =
      (IB n).moduleUnderlying.hom.app M) :
    ∃ d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA,
      d.level = level ∧ @d.restriction = @restriction ∧
      IsIso (CategoryTheory.SystemEvaluationNormalization.derivedMate adjB adjA d.scalar) ∧
      (∀ n : ℕ, IsIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
        (adjn n) adj0 (d.level n))) ∧
      (∀ {n m : ℕ} (h : n ≤ m),
        IsIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
          (adjn n) (adjn m) (d.restriction h))) ∧
      (∀ (n : ℕ) (Z : DerivedCategory (StrictRingSystem BX)),
        (singletonLevelRestriction aY n).mapDerivedCategory.map
            ((SystemEvaluationNormalization.derivedMate adjB (adjn n) (FB.evaluation n)).app Z) ≫
          (SystemEvaluationNormalization.derivedMate (adjn n) adj0 (d.level n)).app
            ((derivedSystemEvaluation BX n).obj Z) =
        (systemNormalizationDerivedRestrictionEvaluation aY n).inv.app
            (HB.rightDerivedFunctor.obj Z) ≫
          (derivedSystemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n).map
            ((SystemEvaluationNormalization.derivedMate adjB adjA d.scalar).app Z) ≫
          (CategoryTheory.SystemEvaluationNormalization.derivedMate adjA adj0 (FA.evaluation n)).app
              ((systemNormalizationRestriction aX).mapDerivedCategory.obj Z) ≫
          H0.rightDerivedFunctor.map
            ((systemNormalizationDerivedRestrictionEvaluation aX n).hom.app Z)) ∧
      (∀ {n m : ℕ} (h : n ≤ m) (Z : DerivedCategory (StrictRingSystem BX)),
        (systemDerivedTransition BY h).app (HB.rightDerivedFunctor.obj Z) ≫
            (systemRestriction BY h).mapDerivedCategory.map
              ((SystemEvaluationNormalization.derivedMate adjB (adjn n)
                (FB.evaluation n)).app Z) ≫
            (SystemEvaluationNormalization.derivedMate (adjn n) (adjn m)
              (d.restriction h)).app
            ((derivedSystemEvaluation BX n).obj Z) =
          (SystemEvaluationNormalization.derivedMate adjB (adjn m) (FB.evaluation m)).app Z ≫
            (Hn m).rightDerivedFunctor.map ((systemDerivedTransition BX h).app Z)) := by
  obtain ⟨d, hd, hr, hs, hl, ht⟩ := SystemRestrictionMateCoherenceData
    AY AX BY BX aY aX uTop IA IB FB FA HB HA adjB adjA Hn adjn H0 adj0
    htransition halgebra level levelUnderlying restriction restrictionUnderlying
  obtain ⟨hc, htc⟩ := SystemRestrictionMateCoherenceEquations
    AY AX BY BX aY aX uTop IA IB FB FA HB HA adjB adjA Hn adjn H0 adj0 d
  exact ⟨d, hd, hr, hs, hl, ht, hc, htc⟩

end SheafOfModules
