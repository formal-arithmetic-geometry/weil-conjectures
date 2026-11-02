/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Open direct image for the three ell-adic coefficient rings

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sk-prop-open-coefficients/
_section.md and sk-prop-open-coefficients.proof.md
(blueprint: lem-sfb-admissible-direct-image).

The three conjuncts use the existing finite constant scalar local-model definition
of bounded constructibility and the ordinary ambient right derived module direct image.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Direct image along a quasi-compact open immersion preserves bounded constructibility
for integral, finite-extension and algebraic-closure coefficients.
Source: blueprint sk-prop-open-coefficients, statement and proof
(blueprint: lem-sfb-admissible-direct-image).

We realize the finite extension inside the fixed algebraic closure, with its induced
valuation topology, as in the coefficient framework. Its ring of integers is
`Profinite.padicIntegersRingObj`; the algebraic-closure ring uses sections taking values
in one finite subextension. All three coefficient rings are pulled back by `condensedRingObj`.

Proof:
1. For O_E, apply det-thm-sf-pf-adic-open (any field with characteristic different from ell,
   so both standing field cases): Rj_* commutes with derived inverse limits and cones, so
   Rj_*K is derived complete and its reduction modulo the uniformizer is Rj_* of the
   reduction of K. The reduction comes from the etale site; Tag 09A6 identifies its direct
   image with the pullback of the etale one, bounded constructible by open finiteness, and
   the integral criterion gives Rj_*K in Dbc(X, O_E).
2. For E and Qlbar, det-lem-integral-models-generators (integral-models(4)) expresses the
   input by finite cones and shifts of coefficient extensions of integral
   C = a_!L_0 in Dbc(U, O_E). Step 1 makes H = Rj_*C integral bounded constructible; j is
   qcqs and C is bounded.
3. lem-sfb-localized-direct-image-comparison identifies the E-image of C[1/ell] with
   E_X ⊗^L H, and lem-sfb-qlbar-direct-image-comparison identifies the Qlbar-image with
   Qlbar_X ⊗^L_{E_X} (E_X ⊗^L H); their proofs carry the two bounded-continuity colimits
   (telescope inverting ell, finite subextensions). lem-sfb-open-rational-scalar-local-models
   keeps the inputs bounded below and makes both scalar extensions of H bounded
   constructible in the finite constant local model convention.
4. The module pushforward is additive and left exact (sk-def-sfb-module-pushforward-pullback)
   on a Grothendieck module category (lem-sfb-modobj-grothendieck), so Rj_* is triangulated
   (lem-weil-pbc-derived-direct-image-triangulated). The rational Dbc categories are
   triangulated (sk-cor-coefficient-heart-ii); induction through the finite cone-and-shift
   construction of step 2 gives both rational conclusions.
-/
theorem constantModelBoundedConstructible_open_coefficient_direct_image
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (Finite k ∨ IsAlgClosed k)] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) U)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) U K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) j).obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) U)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) U K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObj E) j).obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) U K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) j).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
