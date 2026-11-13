/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-!
# Pasting of module base change maps

## References

* [Stacks, Cohomology, Remarks 0ATM and 08HY]
* [Stacks, Sheaves, Lemmas 0096 and 0097]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

private noncomputable abbrev adj {A B : Scheme.{u}} (k : A ⟶ B) :=
  Classical.choose (exists_tensorPullbackAdjunction k)

private noncomputable def pushforwardSquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hsq : g' ≫ f = f' ≫ g) :
    TwoSquare (pushforward g') (pushforward f') (pushforward f) (pushforward g) :=
  TwoSquare.mk _ _ _ _
    ((pushforwardComp g' f).hom ≫ (pushforwardCongr hsq).hom ≫
      (pushforwardComp f' g).inv)

private noncomputable def baseChangeSquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hsq : g' ≫ f = f' ≫ g) :
    TwoSquare (pushforward f) (tensorPullback g') (tensorPullback g) (pushforward f') :=
  (mateEquiv (adj g') (adj g)).symm (pushforwardSquare f f' g g' hsq)

private theorem baseChangeSquare_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hsq : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (baseChangeSquare f f' g g' hsq).app F = moduleBaseChangeMap f f' g g' hsq F := by
  apply ((adj g).homEquiv _ _).injective
  dsimp only [adj, Functor.comp_obj]
  rw [moduleBaseChangeMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (adj g') (adj g)
    (pushforwardSquare f f' g g' hsq) F).symm

private theorem pushforwardSquare_pasting
    {X S X' S' X'' S'' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : S'' ⟶ S') (h' : X'' ⟶ X')
    (hsq₁ : g' ≫ f = f' ≫ g) (hsq₂ : h' ≫ f' = f'' ≫ h)
    (hsq : (h' ≫ g') ≫ f = f'' ≫ (h ≫ g)) :
    pushforwardSquare f f'' (h ≫ g) (h' ≫ g') hsq =
      ((TwoSquare.hComp (pushforwardSquare f' f'' h h' hsq₂)
        (pushforwardSquare f f' g g' hsq₁)).whiskerTop
          (pushforwardComp h' g').inv).whiskerBottom (pushforwardComp h g).hom := by
  apply NatTrans.ext
  funext M
  apply hom_ext
  intro U
  simp only [pushforwardSquare, TwoSquare.hComp, TwoSquare.whiskerTop,
    TwoSquare.whiskerBottom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id]
  change M.presheaf.map _ = M.presheaf.map _ ≫ M.presheaf.map _
  rw [← Functor.map_comp]
  congr 1

/-- Underived module base change maps paste along horizontal commutative squares
(Stacks, Remarks 08HY and 0ATM; Lemmas 0096 and 0097). -/
theorem moduleBaseChangeMap_pasting
    {X S X' S' X'' S'' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : S'' ⟶ S') (h' : X'' ⟶ X')
    (hsq₁ : g' ≫ f = f' ≫ g) (hsq₂ : h' ≫ f' = f'' ≫ h) (F : X.Modules) :
    moduleBaseChangeMap f f'' (h ≫ g) (h' ≫ g')
        ((Category.assoc h' g' f).trans
          ((congrArg (fun k ↦ h' ≫ k) hsq₁).trans
            ((Category.assoc h' f' g).symm.trans
              ((congrArg (fun k ↦ k ≫ g) hsq₂).trans (Category.assoc f'' h g))))) F =
      ((conjugateIsoEquiv
          ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
            (Classical.choose (exists_tensorPullbackAdjunction h)))
          (Classical.choose (exists_tensorPullbackAdjunction (h ≫ g)))).symm
          (pushforwardComp h g)).hom.app ((pushforward f).obj F) ≫
        (tensorPullback h).map (moduleBaseChangeMap f f' g g' hsq₁ F) ≫
        moduleBaseChangeMap f' f'' h h' hsq₂ ((tensorPullback g').obj F) ≫
        (pushforward f'').map
          (((conjugateIsoEquiv
            ((Classical.choose (exists_tensorPullbackAdjunction g')).comp
              (Classical.choose (exists_tensorPullbackAdjunction h')))
            (Classical.choose (exists_tensorPullbackAdjunction (h' ≫ g')))).symm
            (pushforwardComp h' g')).inv.app F) := by
  let c := (conjugateIsoEquiv ((adj g).comp (adj h)) (adj (h ≫ g))).symm
    (pushforwardComp h g)
  let c' := (conjugateIsoEquiv ((adj g').comp (adj h')) (adj (h' ≫ g'))).symm
    (pushforwardComp h' g')
  let hsq := (Category.assoc h' g' f).trans
    ((congrArg (fun k ↦ h' ≫ k) hsq₁).trans
      ((Category.assoc h' f' g).symm.trans
        ((congrArg (fun k ↦ k ≫ g) hsq₂).trans (Category.assoc f'' h g))))
  have hc : conjugateEquiv ((adj g).comp (adj h)) (adj (h ≫ g)) c.hom =
      (pushforwardComp h g).hom := by
    simp [c]
  have hc' : conjugateEquiv (adj (h' ≫ g')) ((adj g').comp (adj h')) c'.inv =
      (pushforwardComp h' g').inv := by
    simp [c']
  have key : baseChangeSquare f f'' (h ≫ g) (h' ≫ g') hsq =
      ((TwoSquare.vComp (baseChangeSquare f f' g g' hsq₁)
        (baseChangeSquare f' f'' h h' hsq₂)).whiskerLeft c'.inv).whiskerRight c.hom := by
    apply (mateEquiv (adj (h' ≫ g')) (adj (h ≫ g))).injective
    rw [mateEquiv_conjugateEquiv_vcomp _ ((adj g).comp (adj h)),
      conjugateEquiv_mateEquiv_vcomp _ ((adj g').comp (adj h')),
      mateEquiv_hcomp, hc, hc']
    simp only [baseChangeSquare, Equiv.apply_symm_apply]
    exact pushforwardSquare_pasting f f' f'' g g' h h' hsq₁ hsq₂ hsq
  have keyF := congrArg (fun w ↦ w.app F) key
  simpa [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    baseChangeSquare_app, c, c'] using keyF


end
end AlgebraicGeometry.Scheme.Modules
