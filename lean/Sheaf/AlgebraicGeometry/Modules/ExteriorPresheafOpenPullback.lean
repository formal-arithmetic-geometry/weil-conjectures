/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

/-!
# Exterior presheaves under open pullback

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-presheaf-open-pullback).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of the sectionwise exterior-power presheaf along an open inclusion is the
sectionwise exterior-power presheaf of the restricted module.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-presheaf-open-pullback).

Proof: For an open inclusion, the left adjoint to presheaf pushforward is restriction to
image opens, followed by scalar transport along the inverse of `U.ι.appIso`. Indeed,
image of opens is left adjoint to inverse image of opens, and the unit and counit are the
presheaf restrictions; their triangle identities are the presheaf composition laws.
Thus its universal property identifies this restriction functor with
`PresheafOfModules.pullback U.ι.toRingCatSheafHom.hom`. On an open V of U, the ring
isomorphism identifies O_U(V) with O_X(U.ι ''ᵁ V), and the restricted module has exactly
the sections M(U.ι ''ᵁ V) with scalars transported through this isomorphism. Extend the
map on tuples sending each tuple to its wedge using the exterior-power universal property.
Do this in both directions through the inverse ring isomorphism. The composites are the
identity on pure wedges, hence on the exterior powers by `exteriorPower.linearMap_ext`.
The same pure-wedge test proves naturality with respect to every inclusion V' ⊆ V,
using the defining pure-wedge formula of `exteriorSheafRestriction_existsUnique`.
These component isomorphisms give the asserted presheaf isomorphism. This argument works
also for n = 0 (empty wedges and scalar transport), empty opens, and the empty scheme;
it does not require finite generation or local freeness. -/
theorem exteriorPresheaf_open_pullback {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
      (exteriorSheafPresheaf M n) ≅ exteriorSheafPresheaf (M.restrict U.ι) n) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
