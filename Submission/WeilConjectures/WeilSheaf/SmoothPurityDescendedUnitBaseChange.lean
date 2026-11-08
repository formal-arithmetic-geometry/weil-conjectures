/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents
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
public import Submission.WeilConjectures.SmoothPurity.Defs
public import Submission.WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Unit base change implies universality of the descended Weil smooth trace -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

local instance : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩
local instance : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

local instance : LocallyOfFiniteType (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance : QuasiCompact (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance : IsSeparated (Over.mk X.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))
local instance : LocallyOfFiniteType (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
local instance : QuasiCompact (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))
local instance : IsSeparated (Over.mk Y.hom.geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- The bounded exchange obtained from the geometric fiber of the chosen compactification. -/
noncomputable def descendedShriekGeometricExchange :
    boundedConstructibleLowerShriek l f ⋙
        boundedConstructibleUpperStarOfMap l Y.hom.geometricFiberProj ≅
      boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
        boundedConstructibleLowerShriek l (traceGeometricFiberOverMap f) :=
  purityFieldLowerShriekExchange l f (traceGeometricFiberOverMap f)
    (compactificationOverField f) ((compactificationOverField f).geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).i
      ((compactificationOverField f).i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).g rfl).flip

end AlgebraicGeometry.ProEtale.CondensedRing
