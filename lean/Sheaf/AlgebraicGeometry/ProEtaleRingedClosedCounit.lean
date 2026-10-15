/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying

/-! Ringed pro-etale localization: a geometric step of the open-closed argument. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The closed inverse-image/direct-image adjunction is a reflection for arbitrary
ring-sheaf coefficients. The adjunction is specified on the concrete functors.

Source: Stacks Project, Tag 09AA and Tags 09BK/09BL
(blueprint: lem-weil-pbc-proetale-ringed-closed-counit).

Proof: Work on affine opens of the target and use the affine ind-etale basis.
The closed-site lift `v` is left adjoint to base change `b`, with `b(v(W)) = W`.
For each basis object `W`, this adjunction identifies the inverse-image indexing
category with the opposite of a category having initial object `v(W)`. Its colimit
is thus evaluation at `v(W)`. Applied to a direct image of `H`, this evaluation is
`H(b(v(W))) = H(W)`. The resulting presheaf is already a sheaf on the basis;
sheafification identifies the canonical counit with the identity. Hence the counit
is invertible on every affine basis, and its naturality glues these inverses over
affine intersections. Multiplication naturality of inverse image and the ring-unit
action on direct image show that this counit and its inverse are module maps.
The conclusion holds for every adjunction on the specified functors by uniqueness
of adjoints, since changing adjunction conjugates the counit by an isomorphism. -/
theorem proEtale_ringed_closed_counit {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
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
    ∀ H, IsIso (ai.counit.app H) := by
  sorry

end AlgebraicGeometry.Scheme
