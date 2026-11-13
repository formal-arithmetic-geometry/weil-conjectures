/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassEquiv
import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkNormalization

/-! # Local direct-image stalks and total cohomology

## References

* [Stacks, Tags 02OD and 01E4]
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

/-- On the local spectrum, the stalk of the direct image of a higher direct
image equals total cohomology. The equivalence inverts every compatible restricted
resolution section-class map, followed by restriction to the corresponding open
(Stacks, Tags 02OD, 01E4 and 01FB). -/
theorem localDirectImage_stalk_cohomology {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) :
    ∃ e : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
          p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)))
      ≃ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F),
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
          (e.toLinearMap (TopCat.Presheaf.germ
            ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
              (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
                p).obj
                ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj
                  F))).presheaf V y hy (D.targetClass p xi))) = xi := by
  have h := localDirectImage_stalk_cohomology_equiv f y F p
  cases h with
  | intro e he =>
    refine ⟨e.symm, ?_⟩
    intro I K V hy D xi
    exact localDirectImage_stalk_cohomology_normalization f y F p e he I K V hy D xi


end AlgebraicGeometry
