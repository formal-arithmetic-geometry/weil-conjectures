/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Module base change maps and open restriction

Source: Stacks Project, Tags 02KG, 0ATL, 0ATM, 00A0 and 08HY
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The module base change map is adjoint to the pushforward of the pullback unit,
using the sectionwise identification of composite pushforwards.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction). -/
def moduleBaseChangeMap {X S T X₁ : Scheme.{u}}
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

/-- Naturality of the adjoint-defined base change map.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction).
Proof: the unit is natural in F; pushforward and the sectionwise composition
identifications preserve that equality. Naturality of the adjunction Hom bijection
then gives the displayed equality. This is the naturality clause preceding step (1). -/
theorem moduleBaseChangeMap_naturality {X S T X₁ : Scheme.{u}}
    (f : X ⟶ S) (f₁ : X₁ ⟶ T) (u₁ : T ⟶ S) (v : X₁ ⟶ X)
    (h : v ≫ f = f₁ ≫ u₁) {F G : X.Modules} (φ : F ⟶ G) :
    (tensorPullback u₁).map ((pushforward f).map φ) ≫ moduleBaseChangeMap f f₁ u₁ v h G =
      moduleBaseChangeMap f f₁ u₁ v h F ≫
        (pushforward f₁).map ((tensorPullback v).map φ) := by
  unfold moduleBaseChangeMap
  apply (Classical.choose (exists_tensorPullbackAdjunction u₁)).homEquiv_naturality_right_square
  let e := Classical.choose (exists_tensorPullbackAdjunction v)
  let t : pushforward f ⟶ tensorPullback v ⋙ pushforward v ⋙ pushforward f :=
    Functor.whiskerRight e.unit (pushforward f)
  let q : pushforward v ⋙ pushforward f ⟶ pushforward f₁ ⋙ pushforward u₁ :=
    (pushforwardComp v f).hom ≫ (pushforwardCongr h).hom ≫ (pushforwardComp f₁ u₁).inv
  exact (t ≫ Functor.whiskerLeft (tensorPullback v) q).naturality φ


end
end AlgebraicGeometry.Scheme.Modules
