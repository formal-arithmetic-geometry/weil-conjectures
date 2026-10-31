/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationNormalizationData

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-scalar-mate-invertibility).
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

/-- Scalar restriction of strict systems commutes with the geometric derived direct image.

Source: Stacks Project, Tag 0D6E, via the sequence-site realization of Zheng,
Construction 4.1 (blueprint: lem-route-system-restriction-scalar-mate-invertibility).

Proof: Transport the strict-system categories to modules on the ringed sequence sites.
The given transition equations identify FB and FA with componentwise geometric inverse
image on these sites, and the coefficient equation gives a commuting square of the
sequence ring sheaves. Scalar restriction is the direct image of the identity-topos
coefficient morphism. Form the common composite ringed morphism in its two ways. The
unbounded derived pushforward-composition theorem gives invertible comparisons from
both composites to the derived direct image of the common morphism. Restriction is
exact, so its derived direct image is its termwise localization. The ordinary comparison
is the mate of d.scalar.inv: transpose its components under the two module adjunctions;
d.scalarEvaluation and the underlying comparison identify their transposes with the
same underlying sheaf map. The normalized composition-unit equations, followed by the
mixed-derived-mate unit identity, identify the derived comparison with derivedMate.
Right-adjoint uniqueness transports this equality to the supplied adjunctions. Thus its
components, and hence the natural transformation, are invertible. This argument applies
to unbounded complexes and arbitrary coefficient maps; it assumes no flatness. -/
theorem systemRestrictionScalarMateInvertibility
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
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA) :
    IsIso (SystemEvaluationNormalization.derivedMate adjB adjA d.scalar) := by
  sorry

end SheafOfModules
