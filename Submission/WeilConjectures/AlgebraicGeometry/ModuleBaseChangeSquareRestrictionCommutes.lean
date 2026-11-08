/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Components of module base change under restriction

Source: Stacks Project, Sheaves, Tag 00A0 and Cohomology, Tags 0ATL and 0ATM.
(blueprint: lem-weil-pbc-module-square-restriction-commutes).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

private def baseChangeMapCore {X S T X₁ : Scheme.{u}}
    (f : X ⟶ S) (f₁ : X₁ ⟶ T) (u₁ : T ⟶ S) (v : X₁ ⟶ X)
    (h : v ≫ f = f₁ ≫ u₁) (F : X.Modules) :
    (tensorPullback u₁).obj ((pushforward f).obj F) ⟶
      (pushforward f₁).obj ((tensorPullback v).obj F) :=
  ((Classical.choose (exists_tensorPullbackAdjunction u₁)).homEquiv _ _).symm
    ((pushforward f).map
      ((Classical.choose (exists_tensorPullbackAdjunction v)).unit.app F) ≫
      (pushforwardComp v f).hom.app ((tensorPullback v).obj F) ≫
      (pushforwardCongr h).hom.app ((tensorPullback v).obj F) ≫
      (pushforwardComp f₁ u₁).inv.app ((tensorPullback v).obj F))

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
    (baseChangeSquare f f' g g' hsq).app F = baseChangeMapCore f f' g g' hsq F := by
  apply ((adj g).homEquiv _ _).injective
  dsimp only [adj, Functor.comp_obj]
  rw [baseChangeMapCore, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (adj g') (adj g)
    (pushforwardSquare f f' g g' hsq) F).symm


end
end AlgebraicGeometry.Scheme.Modules
