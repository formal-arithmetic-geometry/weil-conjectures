/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Connected limits of the sheafified site left adjoint

Source: Stacks Project, Sites, Tags 00XR and 00XS
(blueprint: lem-sfb-site-left-adjoint-connected-limits).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Source: Stacks Project, Sites, Tags 00XR(1),(2) and 00XS
(blueprint: lem-sfb-site-left-adjoint-connected-limits).

The hypothesis on covering presieves, together with preservation of all pullbacks,
expresses Stacks continuity (00WV). The existential continuity witness records its
consequence for sheaves, using Mathlib's definition of continuity. The right adjoint
is then exactly precomposition, and the left adjoint is the sheafified left Kan
extension, not an unspecified functor. No terminal object is required.

Proof: Continuity implies that precomposition preserves sheaves
[lem-weil-pbc-site-continuous-pushforward-sheaf]. The sheafified Kan extension is
left adjoint to this restriction
[lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction]. At an object V of D,
the presheaf left adjoint is the colimit over the opposite of the category of
pairs (U, V ⟶ i(U)). A common-source span in this opposite category is completed
by taking a pullback in C: the universal property of its image under i supplies
the arrow from V. A parallel pair is coequalized by taking an equalizer in C:
the universal property of its image supplies the arrow from V into that image.
These constructions do not require the indexing category to be nonempty.
Thus the two hypotheses of [lem-sfb-almost-filtered-set-colimits] hold, and its
canonical bijections show that the presheaf left adjoint preserves pullbacks
and equalizers, using objectwise presheaf limits
[lem-weil-pbc-presheaf-finite-limits-objectwise]. Limits of sheaves are computed
as presheaf limits [lem-weil-pbc-site-sheaf-sets-limits-sectionwise], and set
sheafification preserves finite limits [lem-weil-pbc-sheafification-sets-exact].
The composite therefore preserves both specified shapes of limits. -/
theorem sheafPullback_preserves_pullbacks_and_equalizers
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (i : C ⥤ D) [i.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map i ∈ K (i.obj X))
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan i]
    [PreservesLimitsOfShape WalkingParallelPair i] :
    ∃ hcontinuous : i.IsContinuous J.toGrothendieck K.toGrothendieck,
      Nonempty (sheafPullbackConstruction.sheafPullback i (Type u)
        J.toGrothendieck K.toGrothendieck ⊣
          @sheafPushforwardContinuous C _ D _ i (Type u) _
            J.toGrothendieck K.toGrothendieck hcontinuous) ∧
      PreservesLimitsOfShape WalkingCospan
        (sheafPullbackConstruction.sheafPullback i (Type u)
          J.toGrothendieck K.toGrothendieck) ∧
      PreservesLimitsOfShape WalkingParallelPair
        (sheafPullbackConstruction.sheafPullback i (Type u)
          J.toGrothendieck K.toGrothendieck) := by
  sorry

end CategoryTheory.Functor
