/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom

/-!
# The equalizer internal hom for the relative monoidal tensor

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
unit sk-prop-sfb-module-category, definition def-sfb-modobj-internal-hom
(blueprint: def-sfb-modobj-internal-hom).

The object and functor are the existing `CategoryTheory.Mod.ihom'`. Its equalizer uses
`homModPre` and `homModB`, with the action through the target given by `homAct`.
The statement below identifies this specified functor as a right adjoint for the
monoidal tensor of `CategoryTheory.Mod.monoidalCategory`, with the factor order of the
blueprint. The existing `ihom'Adjunction` instead uses `Mod.tensorLeft`, the separately
constructed coequalizer functor computing tensoring on the right.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Mod

/-- The equalizer internal hom is right adjoint to left relative tensoring.
Source: main-20261015 blueprint, sec-proetale-coefficients,
sk-prop-sfb-module-category/def-sfb-modobj-internal-hom
(blueprint: def-sfb-modobj-internal-hom).

Here `ihom' R M` is the actual equalizer functor already constructed upstream, with
its action through the target, rather than an unspecified right adjoint.

Proof plan (the node's ten steps):
1. Grothendieck abelianness supplies equalizers and coequalizers; ambient closedness
   makes both tensor functors preserve colimits by
   `lem-weil-pbc-left-adjoint-preserves-colimits` and symmetry.
2. Curry the action-through-target and action-through-source composites to obtain
   the two maps, namely `homModB` and `homModPre`, in the opposite order to the display.
3. Curry evaluation followed by the target action, after moving the scalar past M,
   to obtain `homAct`; its unit and associativity follow by uncurrying.
4. Commutativity of R shows that both equalizer maps are linear for these actions.
5. Restrict the action to their equalizer; uniqueness gives the module laws.
6. The relative coequalizer universal property identifies module maps out of
   L tensor_R M with ambient maps L tensor M to N linear in both variables
   (`def-sfb-modobj-relative-tensor`, `sk-def-sfb-module-objects`).
7. Currying identifies linearity in M with factorization through the equalizer.
8. Linearity in L is precisely linearity of the transposed equalizer lift;
   the equalizer inclusion is monic, so it detects this equation.
9. Currying and uncurrying, followed by equalizer lift and coequalizer descent, give
   inverse natural Hom bijections. These are the existing `ihom'Adjunction`.
10. Compare its coequalizer tensor with the monoidal tensor by the unique isomorphism
    commuting with the quotient maps. Precompose with the descended symmetry of
    `def-sfb-modobj-symmetric-tensor` to obtain the stated factor order.
    Thus every left tensor functor has this right adjoint, proving closedness.
The module category is abelian by `lem-sfb-modobj-abelian`. -/
theorem nonempty_equalizerInternalHomAdjunction
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    (R : C) [MonObj R] [IsCommMonObj R] (M : Mod C R) :
    Nonempty (MonoidalCategory.tensorLeft M ⊣ ihom' R M) := by
  sorry

end CategoryTheory.Mod
