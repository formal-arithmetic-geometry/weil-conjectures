/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

/-- Evaluation compatibility of the finite-site internal-Hom comparison.
Source: the transpose evaluation identity in Bhatt--Scholze, Lemma 6.3.16
(blueprint: new-sfb-finite-site-internal-hom-evaluation; step 1 of
lem-sfb-finite-site-internal-hom-comparison).

Proof in words. By `siteComparisonEvaluationHom_eq_curry` the comparison is the curry of the
inverse tensor comparison followed by `ν_T^*` of evaluation; whiskering a curry by `F K` and
evaluating gives back the uncurried morphism (`MonoidalClosed.whiskerLeft_curry_ihom_ev_app`). -/
theorem finiteSiteInternalHomComparison_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} [IsNoetherian T]
    (K M : _root_.DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((D(ν^*(T)[ModuleCat.{u + 1} A]).obj K) ◁
        siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M) ≫
        (ProEtale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
          (D(ν^*(T)[ModuleCat.{u + 1} A]).obj K)).counit.app
          (D(ν^*(T)[ModuleCat.{u + 1} A]).obj M) =
      (siteComparisonTensorIso (ModuleCat.{u + 1} A) T K).inv.app
          (((Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op K)).obj M) ≫
        D(ν^*(T)[ModuleCat.{u + 1} A]).map
          ((Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M) := by
  let F := D(ν^*(T)[ModuleCat.{u + 1} A])
  let _ : F.Monoidal := siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) T
  rw [siteComparisonEvaluationHom_eq_curry]
  change (F.obj K ◁ MonoidalClosed.curry _) ≫
      (ihom.ev (F.obj K)).app (F.obj M) = _
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rfl

end AlgebraicGeometry.ProEtale.DerivedCategory
