/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap
public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Local direct-image stalks and total cohomology

Source: Stacks Project, Tags 02OD and 01E4.
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

/-- Normalization of the inverse of the specified canonical class map.
Source: Stacks Project, Tags 01E4 and 01FB; Tag 02OD for the local spectrum.
(blueprint: lem-weil-pbc-local-direct-image-stalk-cohomology-normalization)

Proof: For V containing y, c^{-1}V is top. The pullback-square identity therefore
identifies W = g'^{-1}(f^{-1}V) with all of X'. Restriction from X' to W is thus
an isomorphism on module cohomology. Let eta be the unique global class restricting
to xi. Compute its image under localDirectImage_stalk_class using the fixed
injective resolution. Compute germ(D.targetClass p xi) using the supplied K
and the restricted resolution D.target.resolution. The component identity of
D.target.sections identifies the latter section-complex map with restriction
of K; its augmentation identity identifies its degree-zero map with the
restriction unit. Comparing the fixed resolution with K gives augmented
comparison maps, unique up to homotopy. Their maps on homology agree. Naturality
of evaluation, sectionCohomologyTheta, and isoRightDerivedObj then gives
localDirectImage_stalk_class eta = germ(D.targetClass p xi). The hypothesis
he identifies e with this class map. Applying e.symm yields eta, and restricting
eta to W yields xi, as required. This uses only D.target, and works for every
supplied I, K, V and D. It includes p = 0 and zero cohomology modules. -/
theorem localDirectImage_stalk_cohomology_normalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p : ℕ)
    (e : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
      ≃ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
          p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))))
    (he : ∀ x, e x = localDirectImage_stalk_class f y F p x) :
      ∀ (I : InjectiveResolution F)
        (K : InjectiveResolution
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
        (V : Y.Opens) (hy : y ∈ V)
        (D : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
        (xi : (forget₂ _ AddCommGrpCat.{u}).obj
          ((RingedSpace.moduleCohomology
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor
              ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)))),
        Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((Scheme.Modules.restrictAdjunction
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p
          (e.symm.toLinearMap (TopCat.Presheaf.germ
            ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
              (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
                p).obj
                ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj
                  F))).presheaf V y hy (D.targetClass p xi))) = xi := by sorry

end AlgebraicGeometry
