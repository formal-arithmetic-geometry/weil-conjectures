/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralOpenDirectImage.IntegralOpenDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel

import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageLimits

/-!
# Integral open direct image over an arbitrary field

Source: literature/blueprint/latest, `sk-thm-sf-pf-adic/sk-thm-sf-pf-adic-open.md`,
entire current statement (order 2763); Stacks Tags 099L, 09A6 and 09C1
(blueprint: det-thm-sf-pf-adic-open).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralOpenDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- Integral open direct image preserves constructibility over every field whose
characteristic differs from `l`.

Source: the standing-field and open-direct-image clauses of the current blueprint unit,
and Stacks Tags 099L, 09A6 and 09C1 (blueprint: det-thm-sf-pf-adic-open).

Proof: finite type over a field makes `U` and `X` Noetherian and quasi-separated. The
integral criterion gives derived completeness and bounded constructibility of the input
reduction. The internal integral direct-image-limits theorem gives completeness of the
direct image and identifies the canonical residue comparison, including its scalar
pullback square and geometric counit equation. The finite-coefficient open-direct-image
result gives bounded constructibility and finite Tor amplitude after reduction. Isomorphism
invariance transfers these properties to the actual reduction, and the integral criterion
on `X` yields bounded constructibility and its equality with the finite-Tor subcategory.
The argument includes characteristic zero and positive characteristic cases uniformly;
empty opens and identity open immersions are included by the same categorical maps.
-/
theorem integral_open_direct_image_any_field
    (k : Type u) [Field k] (hchar : ringChar k ≠ l)
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) U K) :
    IsDerivedComplete l E X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      (∃! c :
          (AdicCompletion.derivedReduction l E X 0).obj
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ⟶
            (CondensedRing.moduleObjectDerivedPushforward
              (DerivedNakayama.quotientRing l E 1) j).obj
                ((AdicCompletion.derivedReduction l E U 0).obj K),
        IsIso c ∧
          (reductionPullbackMap l E j).app
              ((CondensedRing.moduleObjectDerivedPushforward
                (DerivedNakayama.integerRing l E) j).obj K) ≫
            (CondensedRing.upperStar (DerivedNakayama.quotientRing l E 1) j).mapDerivedCategory.map
              c ≫
            ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (DerivedNakayama.quotientRing l E 1) j).ofNatIsoLeft
                  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                    (DerivedNakayama.quotientRing l E 1) j)).counit.app
              ((AdicCompletion.derivedReduction l E U 0).obj K) =
            (AdicCompletion.derivedReduction l E U 0).map
              (((CondensedRing.derivedUpperStarLowerStarAdjunction
                  (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                      (DerivedNakayama.integerRing l E) j)).counit.app K)) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
        ((CondensedRing.moduleObjectDerivedPushforward (DerivedNakayama.integerRing l E) j).obj
          K) ∧
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
        (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
          DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralOpenDirectImage
