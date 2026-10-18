/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Higher direct images commute with filtered colimits and direct sums

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity/
sk-lem-proper-heart-continuity-direct-image.md
(blueprint: det-proper-heart-continuity-direct-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a quasi-compact, quasi-separated morphism, every integer-degree higher direct
image on pro-étale module sheaves preserves filtered colimits and direct sums. The target
is the category of modules over the direct-image ring sheaf `p_*A`. The input is placed
in degree zero before localization, right derivation and degree-`q` cohomology.

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity/
sk-lem-proper-heart-continuity-direct-image.md and its unit's Complement;
Stacks Project, derived.tex, Tags 015A, 05TH and 013P for the finite-sum calculation
(blueprint: det-proper-heart-continuity-direct-image).

Proof for stage 3:
1. For a filtered diagram `M`, put `K_i = M_i[0]`, with common lower bound zero.
   Module-sheaf colimits agree with underlying abelian-sheaf colimits by
   lem-weil-pbc-module-sheaves-colimits-forgetful, so the termwise colimit is
   `(colim M)[0]`. Apply det-pe-bounded-continuity-direct-image at bound zero.
   Its comparison on each leg is higher direct image of the colimit inclusion.
   Thus it is the canonical `colimit.post` displayed here, in `p_*A`-modules.
2. For a finite family choose bounded-below termwise injective K-injective resolutions
   of the degree-zero inputs as in lem-sc-bounded-below-injective-resolution, on the
   small site model. For arbitrary rings one may use the already published
   `Scheme.ProEt.ringModuleDirectImage_hasKInjectiveResolutions`: boundedness of the
   chosen resolutions is unnecessary in this finite-sum calculation. Finite sums are
   K-injective: component null-homotopies assemble into a finite tuple. Cohomology
   of the block-diagonal differential is the finite sum of the cohomologies, so the
   summed resolution is a quasi-isomorphism, also for the empty family. The sectionwise
   pushforward of det-pe-topos-functoriality-inverse-image preserves finite biproducts.
   Computing the derived functor on these resolutions gives finite-sum preservation.
   Naturality of the derived unit identifies the maps with higher direct images of
   summand inclusions, compatibly with inclusion of one finite subsum in another.
3. The poset of finite subsets of a small set `J`, including the empty subset, is
   small and filtered, with union as an upper bound. The colimit of its finite subsums
   is the whole sum: cocones are exactly families of maps from the individual summands.
   Apply this universal-property description in both module-sheaf categories, whose
   colimits exist by lem-weil-pbc-module-sheaves-colimits-forgetful.
4. Apply Step 1 to the finite-subsum diagram and combine Steps 2 and 3. On each original
   summand the resulting isomorphism is higher direct image of its coproduct inclusion,
   so it is the canonical coproduct comparison. This includes the empty family. -/
theorem properHeartContinuityDirectImage {X Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (A : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    ∀ (q : ℤ),
      (∀ {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
        (M : I ⥤ SheafOfModules.{u + 1} A),
        IsIso (colimit.post M
          (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0 ⋙
            DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q))) ∧
      ∀ (J : Type (u + 1)),
        PreservesColimitsOfShape (Discrete J)
          (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0 ⋙
            DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q) := by
  sorry

end AlgebraicGeometry.ProEtale
