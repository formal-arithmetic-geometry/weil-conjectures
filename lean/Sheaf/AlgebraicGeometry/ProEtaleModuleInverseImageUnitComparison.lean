/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

import Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction

/-! # The canonical comparison of module and abelian inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunct of the forgotten module unit is invertible for every scheme morphism.

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3,
`lemma-pullback-module` and `lemma-adjoint-push-pull-modules`.
(blueprint: new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison).

Proof: Transport both sites to their strict AsSmall models. The transported ring
unit presents the inverse-image ring, by proEtaleModelRingPresentation. Construct
on the actual abelian inverse image the scalar action obtained from that ring
presentation and the abelian unit presentation. Products of unit sections determine
maps out of the scalar/module product. Testing the module laws on these sections
therefore gives a module, and testing the two scalar-action composites shows that
an abelian map is linear precisely when its adjunct is linear. Restricting the
abelian Hom equivalence gives a module adjunction whose underlying unit is exactly
the abelian unit. Compare it with the pullbackPushforwardAdjunction on the small
model by uniqueness of left adjoints. That comparison respects units, so its
underlying inverse is the adjunct of the forgotten module unit and is invertible.
Transport back along AsSmall; precomposition commutes with the forgetful functors
and transports the units, so the same identification holds on the original sites.
Finally compare this adjunction with the supplied ai by uniqueness of left adjoints.
Its unit formula identifies the displayed map with the canonical comparison
composed with the forgotten uniqueness isomorphism. This proves invertibility
for every ai, including the zero ring and empty schemes. No closed immersion is used. -/
theorem proEtaleModuleInverseImage_unitComparison_isIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)) :
    let S := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
    let R := (sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
    ∀ M, IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf S).obj M)
      ((SheafOfModules.toSheaf R).obj ((proEtaleModuleInverseImage i A).obj M))).symm
        ((SheafOfModules.toSheaf S).map (ai.unit.app M))) := by
  sorry

end AlgebraicGeometry.Scheme
