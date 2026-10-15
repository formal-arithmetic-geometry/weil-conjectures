/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! Ringed pro-etale localization: a geometric step of the open-closed argument. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Localization at an open object identifies actual inverse image for an arbitrary
ring-sheaf coefficient with restriction of module sheaves to the slice. There is no
closed-complement or quasi-compactness hypothesis in this comparison.

Source: Stacks Project, Tags 09BN and 00XZ
(blueprint: lem-weil-pbc-proetale-ringed-open-comparison).

Proof: The weakly-etale localization equivalence identifies the site of `U.left`
with the slice at `U`, keeping schemes, maps and covering families unchanged.
For an object already over `U`, the inverse-image indexing category has the
corresponding object as terminal object. Its colimit is evaluation at that object.
This gives a natural ring isomorphism from the inverse-image ring to the slice ring,
compatible with multiplication, and the same evaluation comparison for modules.
Transport modules along that ring isomorphism and the site equivalence to obtain
`q`. The module comparison is natural since it is induced by those same evaluation
maps, and is linear by the multiplication compatibility. These comparisons apply
to the actual inverse image transported through the model-site equivalences: each
such transport preserves the relevant adjunction, and uniqueness of left adjoints
identifies the transported comparison with the specified inverse-image functor. -/
theorem proEtale_ringed_open_comparison {X : Scheme.{u}} (U : X.ProEt)
    [IsOpenImmersion U.hom] (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ q : SheafOfModules.{u + 1}
        ((sheafCompose (ProEt.topology U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)) ≌
          SheafOfModules.{u + 1} (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).over U),
      Nonempty (proEtaleModuleInverseImage U.hom A ⋙ q.functor ≅
        SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) := by
  sorry

end AlgebraicGeometry.Scheme
