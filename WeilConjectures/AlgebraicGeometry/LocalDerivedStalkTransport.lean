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
import WeilConjectures.AlgebraicGeometry.LocalPullbackAdjointStalkIso
import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkCohomology

/-! # Transport of an arbitrary sheaf comparison to local total cohomology

## References

* [Stacks, Tags 02OD, 01E4, 01J7 and 0098]
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

set_option maxHeartbeats 700000 in
-- Elaborating the nested right-derived scalar transports needs additional heartbeats.
/-- An arbitrary isomorphism beta from the local pullback of G to the local higher
direct image transports the stalk of G to total cohomology. If its adjoint sends
a section s to the canonical class of xi, the transported germ restricts to xi. -/
theorem localDerived_stalk_transport {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) (G : Y.Modules)
    (beta : (Scheme.Modules.tensorPullback (Y.fromSpecStalk y)).obj G ⟶
      ((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived p).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    [IsIso beta] :
    ∃ e : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj G ≃ₗ[Y.presheaf.stalk y]
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
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))))
        (s : G.presheaf.obj (op V)),
        Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
            (Y.fromSpecStalk y))).homEquiv _ _ beta) V s = D.targetClass p xi →
        Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((Scheme.Modules.restrictAdjunction
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p
          (e.toLinearMap (TopCat.Presheaf.germ G.presheaf V y hy s)) = xi := by
  let H := ((Scheme.Modules.pushforward
    (pullback.fst (Y.fromSpecStalk y) f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
  let N := (Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj H
  let a : G ⟶ N := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (Y.fromSpecStalk y))).homEquiv _ _ beta
  have ha : IsIso ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map a) :=
    localPullback_adjoint_stalk_isIso Y y G _ beta
  obtain ⟨e, he⟩ := localDirectImage_stalk_cohomology f y F p
  refine ⟨(asIso ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map a)).toLinearEquiv.trans
    e, ?_⟩
  intro I K V hy D xi s hs
  have hg : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map a)
      (TopCat.Presheaf.germ G.presheaf V y hy s) =
        TopCat.Presheaf.germ N.presheaf V y hy (Scheme.Modules.Hom.app a V s) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf _).map a.val)
        (TopCat.Presheaf.germ G.presheaf V y hy s) = _
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
      ((PresheafOfModules.toPresheaf _).map a.val) s
  have hgs : ((asIso ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map a)).toLinearEquiv
      |>.trans e).toLinearMap (TopCat.Presheaf.germ G.presheaf V y hy s) =
        e (TopCat.Presheaf.germ N.presheaf V y hy (D.targetClass p xi)) := by
    change e (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map a)
      (TopCat.Presheaf.germ G.presheaf V y hy s)) = _
    exact (congrArg e hg).trans
      (congrArg (fun t => e (TopCat.Presheaf.germ N.presheaf V y hy t)) hs)
  exact (congrArg
    (Scheme.Modules.moduleCohomologyFMap
      ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
      ((Scheme.Modules.restrictAdjunction
        ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p)
    hgs).trans (he I K V hy D xi)

end AlgebraicGeometry
