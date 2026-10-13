/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap
public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Restriction compatibility of the local stalk class map

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

/-- The canonical stalk class of a global class agrees with the class computed using
an arbitrary supplied target resolution after restriction to the inverse-image open.
Source: Stacks Project, Lemma 20.7.3 (Tag 01E4) and Remark 20.14.2 (Tag 01FB).
(blueprint: lem-weil-pbc-local-direct-image-stalk-class-restriction)

Proof: Write F' for the tensor pullback and W for the inverse-image open. Choose the
fixed injective resolution R used by localDirectImage_stalk_class. Lift the identity
of F' from R to K; its augmentation equation makes the lift unique up to homotopy.
Restrict this lift to W and compare with D.target.resolution using the inverse of
D.target.comparison. The equation D.target.augmentation makes the resulting lift
an augmented lift of the restriction unit. In the construction of the cohomology
restriction map, compute using this lift followed by an injective replacement of
the pushed restricted resolution. Its section map is a quasi-isomorphism (01EZ);
cancel that map and its inverse on homology, as in 01FB. Independence of the choices
then identifies this computation with moduleCohomologyFMap. Degreewise, the equation
D.target.components identifies the section map with restriction of K. Naturality
of evaluation and its homology comparison, of the sheafification unit and counit
in sectionCohomologyTheta, and of isoRightDerivedObj identifies D.targetClass of
the restricted class with restriction of the top class computed from R. Taking
the germ cancels restriction from top to V. This proves the equality, for every
global class eta, including degree zero and zero modules. Neither surjectivity of
restriction nor an inverse to the stalk class map is used. -/
theorem localDirectImage_stalk_class_restriction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p : ℕ)
    (I : InjectiveResolution F)
    (K : InjectiveResolution
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (V : Y.Opens) (hy : y ∈ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
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
                ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj
                  F))).presheaf V y hy (D.targetClass p
          (Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((Scheme.Modules.restrictAdjunction
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
              ((Scheme.Modules.tensorPullback
                (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p eta)) := by
  sorry

end AlgebraicGeometry
