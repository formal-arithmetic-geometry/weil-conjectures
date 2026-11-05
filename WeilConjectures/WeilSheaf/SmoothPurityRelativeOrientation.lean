/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedRelativeUnit
public import WeilConjectures.WeilSheaf.SmoothPurityRelativeOrientationInput
public import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent

/-! # The relative Frobenius-compatible orientation -/

set_option profiler true
set_option profiler.threshold 0

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


/-- Relative smooth purity at the coefficient unit, for any right adjoint of compact
support. The isomorphism lives in the Weil category and hence respects Frobenius. -/
theorem purity_nonempty_relative_shriekRightAdjoint_adicConstant_iso
    (d : ℕ) [SmoothOfRelativeDimension d f]
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J) :
    Nonempty (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨α⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k₀ l X d
  let e := (Functor.Monoidal.εIso (CondensedRing.boundedConstructibleUpperStarOfMap l
    (X := Over.mk (Y ↘ Spec (CommRingCat.of k₀)))
    (Y := CondensedRing.geometricFiberOver (Over.mk (Y ↘ Spec (CommRingCat.of k₀))))
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)).symm
  have := CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_relative l
    (Over.homMk (U := Over.mk (X ↘ Spec (CommRingCat.of k₀)))
      (V := Over.mk (Y ↘ Spec (CommRingCat.of k₀))) f (comp_over f _)) e.hom
  exact nonempty_shriekRightAdjoint_adicConstant_iso_of_unitBaseChange f d α e adj

/-- Forgetting the relative orientation gives the original Frobenius-commuting equation,
with an arbitrary exceptional right adjoint supplied explicitly. -/
theorem purity_exists_forget_relative_shriekRightAdjoint_adicConstant_iso
    (d : ℕ) [SmoothOfRelativeDimension d f]
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ J) :
    ∃ g : forget.obj (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          (J.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫ g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨o⟩ := purity_nonempty_relative_shriekRightAdjoint_adicConstant_iso f d adj
  exact ⟨forget.mapIso o, ((Endofunctor.IsoAlgebra.derivedStrIso _).hom.naturality o.hom.hom).symm⟩

end AlgebraicGeometry.WeilComplex
