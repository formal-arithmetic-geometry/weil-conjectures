/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityNativeTrace
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
public import Submission.WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedAdjunction
public import Submission.WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import Submission.WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import Submission.WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Submission.WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ExchangeConjugate
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality
public import Submission.WeilConjectures.SmoothPurity.Defs
public import Submission.WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # A universal descended compact-support trace gives a native orientation -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

local instance : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩

variable {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

local instance : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance : LocallyOfFiniteType (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)))
local instance : QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)))
local instance : IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (Y ↘ Spec (CommRingCat.of k₀)))

variable (d : ℕ) (T : WeilComplex k₀ l X) (U : WeilComplex k₀ l Y)
  (eT : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l X).functor.obj T.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d)).obj)
  (eU : (ProEtaleWeilSheaf.derivedEquivCondensed k₀ l Y).functor.obj U.obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (Y ↘ Spec (CommRingCat.of k₀))).mapDerivedCategory.obj (𝟙_ _))

end AlgebraicGeometry.WeilComplex
