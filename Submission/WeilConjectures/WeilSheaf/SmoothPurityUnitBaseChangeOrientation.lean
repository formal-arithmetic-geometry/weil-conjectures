/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityTraceUnit

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityNativeUnitOrientation
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityDescentSingle
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
public import Submission.WeilConjectures.WeilSheaf.UpperShriek

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The cyclotomic Weil orientation from geometric unit base change -/

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

local instance : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ Fact.out⟩
local instance : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)⟩
local instance : LocallyOfFiniteType
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance : QuasiCompact
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance : IsSeparated
    (Over.mk ((Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
local instance : LocallyOfFiniteType
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
local instance : QuasiCompact
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
local instance : IsSeparated
    (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))


variable (d : ℕ) [SmoothOfRelativeDimension d f]
  (α : (ProEtaleWeilSheaf.toCondensed k₀ l X).obj
      (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
      (X ↘ Spec (CommRingCat.of k₀))).obj (ProEtale.tateTwist X l d))
    (e : (CondensedRing.boundedConstructibleUpperStarOfMap l
      (X := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
      (Y := Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure))
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).obj
        (CondensedRing.smoothTraceUnit l (Over.mk (Y ↘ Spec (CommRingCat.of k₀)))) ≅
      CondensedRing.smoothTraceUnit l
        (Over.mk ((Over.mk (Y ↘ Spec (CommRingCat.of k₀))).hom.geometricFiberToAlgebraicClosure)))
    [IsIso (CondensedRing.smoothUnitBaseChange l
      (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
        (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _))
      (CondensedRing.traceGeometricFiberOverMap
        (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)))
      (CondensedRing.descendedShriekGeometricExchange l
        (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
          (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _))) e.hom)]

include α e

variable [HasUpperShriek k₀ l f]

end AlgebraicGeometry.WeilComplex
