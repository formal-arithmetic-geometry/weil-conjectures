/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Pasting of module base change maps

Source: Stacks Project, Cohomology, Remarks 0ATM and 08HY; Sheaves, Lemmas 0096 and 0097
(blueprint: lem-weil-pbc-module-base-change-map-pasting).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- Underived module base change maps paste along horizontal commutative squares.
Source: Stacks Project, Cohomology, Remarks 08HY and 0ATM (the derived version), and
Sheaves, Lemmas 0096 and 0097 (the module adjunction and composition identifications).
(blueprint: lem-weil-pbc-module-base-change-map-pasting)

The base change map `β` of a square and its naturality in `F` (the definitional clauses of
the node) are the landed `moduleBaseChangeMap` and `moduleBaseChangeMap_naturality`
(lem-weil-pbc-module-base-change-map-open-restriction). The composition isomorphism
`c_{b,a}` of the node is the inverse of
`(conjugateIsoEquiv ((adj b).comp (adj a)) (adj (a ≫ b))).symm (pushforwardComp a b)`,
`adj k` the canonical adjunction `Classical.choose (exists_tensorPullbackAdjunction k)`:
the conjugate of `(b ∘ a)_* = b_* a_*` is the unique isomorphism compatible with the units.

Proof, following the four steps of the node:
1. Use the canonical adjunction of `def-pc-module-pullback`: a morphism is determined by
its adjoint, the unit is natural, and sectionwise pushforward composes (0096, 0097).
2. `β` is the inverse Hom equivalence applied to the pushforward of the top-arrow unit,
natural in `F` since both naturality composites have the same adjoint.
3. Compose the two adjunctions (`def-weil-pbc-composite-adjunction`) and conjugate the
pushforward composition isomorphism (`lem-weil-pbc-conjugate-iso-unit-equation`). This
produces the unique pullback composition isomorphism compatible with the composite unit.
4. Take the adjoint of the displayed four-arrow composite. (a) Unit compatibility for
`c_{g,h}` replaces the outer unit by the composite unit. (b) Naturality of the unit for `h`
moves it past the pullback of the first base change map. (c) The defining adjoint equation
of the second base change map replaces that map by the pushforward of the unit for `h'`.
(d) The defining equation of the first map replaces it by the pushforward of the unit
for `g'`. (e) Unit compatibility for `c_{g',h'}` identifies the resulting composite with
the unit for `g' ∘ h'`. Thus the adjoint is the pushforward by `f` of this unit, which
is also the defining adjoint of the outer base change map; injectivity of the Hom
equivalence gives the pasting equality. -/
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
  sorry

end
end AlgebraicGeometry.Scheme.Modules
