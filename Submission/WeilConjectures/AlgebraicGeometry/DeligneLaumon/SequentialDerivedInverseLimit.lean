/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Localization.Predicate

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The sequential derived-limit property for a derived strict tower

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-derived-inverse-limit; Stacks Tags 08TC and 07KC
(blueprint: def-weil-pbc-derived-inverse-limit).

Evaluation retains the transitions of a strict tower. Localization transports this
entire inverse system. The derived-limit predicate makes no selection of a cone or functor.

## Main definitions

* `adicDerivedTowerEvaluation`: evaluation of the full derived inverse system.
* `IsAdicSequentialDerivedLimit`: existence of its distinguished Roos triangle.
-/

@[expose] public section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Select the recorded locally-bijective description at the coefficient size t+1.
This is the existing small-site transport, with its size supplied explicitly; imported
max-universe instances otherwise leave an unresolved universe metavariable.
Source: Stacks Tag 03DA; blueprint def-weil-pbc-derived-inverse-limit
(blueprint: def-weil-pbc-derived-inverse-limit). -/
noncomputable instance (priority := 1100) adicModuleLocallyBijective (T : Scheme.{t}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : Scheme.AdicCoefficientDatum A)

end AlgebraicGeometry.ProEtale
