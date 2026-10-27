/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.CategoryTheory.SystemEvaluationNormalizationData

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-pur-system-restriction-mate-coherence).
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
(blueprint: lem-pur-system-restriction-mate-coherence).

Proof: For each level, the identity between underlying inverse-image sheaves is linear
by the compatible ring square; transport it through the specified underlying module
isomorphisms. The same construction level by level respects strict transitions because
the transition equation of each geometric inverse image identifies both paths with the
inverse image of the original transition. This constructs d. On the sequence sites and
on each level site, scalar restriction is the direct image of the identity-topos
coefficient morphism. The two factorizations of the common ringed morphism give the
invertible derived comparisons by derived pushforward composition, including for
nonflat coefficient maps. Their unit equations, or equivalently the counit transpose,
identify them with the derived mates of d. Localize d.scalarEvaluation and the ordinary
transition square using exact-functor localization. Taking the four mates of the scalar
cube gives the scalar identity. Transpose the transition identity under the level
adjunction: mate/counit equations replace the two evaluation mates by evaluated
counits, naturality moves the transition across the counit, and the localized ordinary
transition square identifies the results. Finally cancel the invertible restriction
mate to obtain the displayed restriction-form transition identity. -/
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
  sorry

end SheafOfModules
