/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData
import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointEventualJetSystem
import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSmoothMember

/-!
# High-degree systems through prescribed points with smooth members

Source: blueprint main-20261015, proof of lem-zl-bertini-finite-cover-curve, paragraph 2;
Stacks Project, Varieties, Tags 0FD5 and 0FD6; Coherent, Tag 0B5T.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system).

The kernel is presented by a finite basis: every section vanishing on the reduced finite
set has a unique coefficient tuple. Thus its affine parameter space is literally the affine
space in these coordinates. First-order values use the canonical model
`(m / m²) ⊗[O_x] L_x`. Since `m` annihilates `m / m²`, this is canonically
`(m / m²) ⊗[κ(x)] (L_x ⊗[O_x] κ(x))`, and at a closed point over the algebraically
closed field it is the tensor product over `k` displayed in the source.
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local instance] cachedSheafify cachedWEquals

attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

attribute [local irreducible] tensorPullback tensorPullbackObj
  ProjectiveSpace.homOfGeneratingSections tensorSectionsUnit

attribute [local irreducible] prescribedPointJet prescribedPointRestrictedFamily
  prescribedPointCombination prescribedPointMember prescribedPointVanishes

set_option maxHeartbeats 800000 in
-- The unchanged dependent signature and its section-type conversions need this budget.
end

end AlgebraicGeometry
