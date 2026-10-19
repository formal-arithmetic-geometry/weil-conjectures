/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSheafAffineTopologicalInvariance
import Sheaf.AlgebraicGeometry.ProEtaleSheafEquivalenceZariskiLocal

/-! Direct-image part of pro-etale topological invariance.

Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening` (blueprint:
lem-trf-proetale-topological-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The direct image on set sheaves is an equivalence under a universal homeomorphism.
This is the direct-image clause of Tag 09AB; once established, the adjunction in
`ProEtaleSheafTopologicalInvariance` formally supplies the inverse-image clause and
invertibility of its unit and counit.
Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`.
Proof: Restrict to the standard affine open cover of Y. Each pullback of r is still
universally homeomorphic, so affine topological invariance applies. The open-cover
locality theorem then gives equivalence of the global direct image.
(blueprint: lem-trf-proetale-topological-invariance-direct-image)
-/
theorem proEtaleSheafDirectImage_topological_invariance {X Y : Scheme.{u}} (r : X ⟶ Y)
    (hr : (topologically IsHomeomorph).universally r) :
    (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence := by
  apply proEtaleSheafDirectImage_isEquivalence_of_openCover r Y.affineCover
  intro i
  apply proEtaleSheafDirectImage_affine_topological_invariance
  exact (topologically IsHomeomorph).universally.pullback_snd r (Y.affineCover.f i) hr

end AlgebraicGeometry.Scheme
