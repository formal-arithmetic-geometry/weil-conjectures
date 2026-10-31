/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmallEnlargedEtaleModules

/-!
# Restriction between the small étale sites of enlarged objects

Source: Stacks Project, Tags 03G0, 03LP and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).

This interface retains the enlarged ringed-site model and supplies the continuity
needed to use its actual small-site restriction functors in descent data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Every arrow between objects étale over the same space is chartwise étale.
Source: Stacks, Tags 03FV, 03G0 and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: take a scheme chart of the source and a scheme atlas of the target. Their
fibre product is a scheme by the representable diagonal. Its two maps to the common
base are étale. Scheme étale cancellation makes the map between the scheme charts
étale. Étale source descent then gives the asserted chartwise condition. This is
exactly the cancellation used to identify the enlarged site with its localization
in the node's final paragraph; no representability of the enlarged arrow is assumed. -/
theorem enlargedArrow_chartwise (H : AlgebraicSpace S)
    {A B : H.EnlargedEtaleSite} (f : A ⟶ B) : IsChartwiseEtale f.hom.left := by
  sorry

/-- Postcomposition by a chartwise étale map is continuous on the scheme-object sites.
Source: Stacks, Tag 03LP, its proof, and Tag 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the functor leaves the underlying schemes and scheme arrows unchanged.
A covering is therefore still a jointly surjective étale family. Pullbacks of
covering arrows are the same scheme fibre products before and after postcomposition.
Thus a sheaf's covering equalizers remain equalizers under precomposition, proving
continuity. This is the scheme restriction of enlargedPostcompose_continuous,
compatible with enlargedPostcomposeSchemeIso and the comparison equivalences. -/
theorem chartwiseEtaleMap_continuous {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    (chartwiseEtaleMap f hf).IsContinuous X.etaleTopology Y.etaleTopology := by
  sorry

attribute [instance] chartwiseEtaleMap_continuous

end AlgebraicGeometry.AlgebraicSpace
