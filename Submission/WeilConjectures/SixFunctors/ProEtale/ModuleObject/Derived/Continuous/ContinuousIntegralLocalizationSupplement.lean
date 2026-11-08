/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import Mathlib.CategoryTheory.Functor.OfSequence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The localization telescope of integral continuous coefficients -/

@[expose] public section

universe u v w x
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The sequential diagram obtained by repeatedly multiplying an object by ℓ.
Source: Bhatt--Scholze, Lemma 6.8.2, localization telescope.
(blueprint: def-weil-pbc-integral-localization-telescope). -/
abbrev integralLocalizationSequence {C : Type v} [Category.{w} C] [Preadditive C] (K : C) :
    ℕ ⥤ C :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 K)


end AlgebraicGeometry.ProEtale.CondensedRing
