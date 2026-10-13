/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap

/-! # Independence of the top section class

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

/-- The defined local class map can be computed on the top open using any
injective resolution of the pulled-back module.
Source: Stacks Project, Lemma 20.7.3 (Tag 01E4).
(blueprint: lem-weil-pbc-local-direct-image-stalk-class-top-comparison)

Proof: Let R be the fixed injective resolution in localDirectImage_stalk_class
and let h be the first projection. Lift the identity of the pulled-back module
from R to K by InjectiveResolution.desc. The augmentation equation gives
naturality of isoRightDerivedObj for global sections and for pushforward h.
The forgetful homology comparison is natural for this lift. Global sections of
the lift agree degreewise with top sections of its direct image. Naturality of
the exact-sheafification homology comparison and the sheafification counit makes
sectionCohomologyComparison natural; the adjunction makes sectionCohomologyTheta
natural. Evaluate at top and concatenate these squares. The map on homology of
the pushed lift cancels by naturality of isoRightDerivedObj.inv, and the derived
identity map is identity. This identifies the top class maps computed with R and
K. Compose with the top germ and evaluate at eta. The definition of
localDirectImage_stalk_class is exactly the first composite. No restriction to
a smaller open is involved, and the argument works for degree zero and zero
modules without assuming that theta is invertible on sections. -/
theorem localDirectImage_stalk_class_top_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p : ℕ)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (eta : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) :
    localDirectImage_stalk_class f y F p eta =
      TopCat.Presheaf.germ
        ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
          (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
            p).obj
            ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))).presheaf
        ⊤ y (by trivial)
        (Scheme.Modules.Hom.app
          (K.isoRightDerivedObj
            (Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)) p).inv ⊤
          (Scheme.Modules.resolutionSectionClass K
            (((Scheme.Modules.pushforward
              (pullback.fst (Y.fromSpecStalk y) f)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K.cocomplex)
            ⊤ (Iso.refl _) p eta)) := by
  sorry

end AlgebraicGeometry
