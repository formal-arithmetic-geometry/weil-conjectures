/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback

/-! # Finite open coefficient-map compatibility

Source: Stacks Project, Tags 02OD, 01F7 and 01FB: factorization of finite
neighbourhoods and restriction of the underlying sheaf maps.
(blueprint: lem-weil-pbc-formal-functions-finite-open-unit-pasting)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

/-- Restricting the finite coefficient h-map composes the two restricted
pullback units. This is an identity of module-sheaf morphisms, before applying
cohomology, and uses no resolutions beyond the unit-square fields of E and D.
Source: Stacks Project, Tag 02OD, factorization through the local spectrum;
Tags 01F7 and 01FB, composition and restriction of h-maps.
(blueprint: lem-weil-pbc-formal-functions-finite-open-unit-pasting)

Proof: Let g be the local projection, j the finite map, and i the finite
projection; j followed by g equals i. Transpose the definition of
formalFunctionsFiniteFMap along tensorPullback g. Its transpose is the i-unit,
followed by the inverse pushforward-composition identification and the
projection-equality identification. Thus the g-unit followed by g_* of the
finite h-map is the i-unit with these identifications.
Transpose the desired equation under the restriction adjunction for U. Use
E.unit_square to replace the transpose of E.psi with the g-unit followed by
the restriction unit for U'. Naturality of pushforwardComp and pushforwardCongr
moves the pushed-forward restricted finite h-map past these identifications.
The assumed square hτ replaces the U'-restriction unit followed by τ by the
finite h-map followed by the W-restriction unit. The preceding global unit
identity then gives the i-unit followed by that restriction unit. D.unit_square
identifies this with the transpose of D.psi. The remaining composition
identifications agree: on an open subset of U, each is the identity followed by
the restriction map associated to the equality of the two inverse images.
Their equality follows from the presheaf composition law and proof irrelevance.
Cancel the invertible pushforward identifications and use injectivity of the
restriction adjunction homEquiv to obtain the displayed equation.
The argument also applies to empty opens and zero coefficients, when every
component is the zero map; it does not assume any open contains y. -/
theorem formalFunctions_finite_open_unit_pasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (F : X.Modules) (n : ℕ) (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (J : InjectiveResolution ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))
    (V : Y.Opens)
    (E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (formalFibreBaseMap Y y n) F I J V) :
    let g := pullback.snd (Y.fromSpecStalk y) f
    let j := formalFunctionsFiniteι f y n
    let i := formalFibreι f y n
    let U := f ⁻¹ᵁ V
    let U' := g ⁻¹ᵁ U
    let W := i ⁻¹ᵁ U
    let F' := (Scheme.Modules.tensorPullback g).obj F
    let Fₙ := (Scheme.Modules.tensorPullback i).obj F
    ∀ (hle : W ≤ j ⁻¹ᵁ U'),
      let r := j.resLE U' W hle
      let s := g.resLE U U' le_rfl
      let q := i.resLE U W le_rfl
      ∀ (hrs : r ≫ s = q)
        (τ : (Scheme.Modules.restrictFunctor U'.ι).obj F' ⟶
          (Scheme.Modules.pushforward r).obj ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ)),
        (Scheme.Modules.restrictAdjunction U'.ι).unit.app F' ≫
          (Scheme.Modules.pushforward U'.ι).map τ ≫
          (Scheme.Modules.pushforwardComp r U'.ι).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) ≫
          (Scheme.Modules.pushforwardCongr (j.resLE_comp_ι hle)).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) =
        formalFunctionsFiniteFMap f y F n ≫ (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictAdjunction W.ι).unit.app Fₙ) ≫
          (Scheme.Modules.pushforwardComp W.ι j).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) →
        E.psi ≫ (Scheme.Modules.pushforward s).map τ ≫
          (Scheme.Modules.pushforwardComp r s).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) ≫
          (Scheme.Modules.pushforwardCongr hrs).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) = D.psi := by sorry

end AlgebraicGeometry
