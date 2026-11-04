/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeDualizingDescent
public import WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
public import WeilConjectures.SmoothPurity.Defs

/-!
# Absolute purity in finite-base descent coordinates

The native exceptional constant object is descent of the ordinary finite-base
dualizing object. Ordinary smooth purity identifies it with descent of the
root-defined shifted Tate object. The cyclotomic encoding is the remaining
comparison with the native Tate twist.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

local instance : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))

/-- The exceptional constant Weil complex is descent of the root-defined Tate
complex, for a smooth structural map. -/
theorem nonempty_shriekRightAdjoint_adicConstant_descendedTate_iso
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    {R : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ R) :
    Nonempty (R.obj (WeilSheaf.toComplex.obj
      (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))) ≅
      (finiteBaseNativeDescent (k₀ := k₀)).obj
        (CondensedRing.boundedConstructibleTateTwist l
          (Over.mk (X ↘ Spec (CommRingCat.of k₀))) d (2 * d))) := by
  obtain ⟨e⟩ := nonempty_shriekRightAdjoint_finiteBaseNativeDescent_dualizing_iso adj
  have : SmoothOfRelativeDimension d
      (Over.mkIdTerminal.from (Over.mk (X ↘ Spec (CommRingCat.of k₀)))).left :=
    ‹SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))›
  exact ⟨R.mapIso finiteBaseNativeDescentUnitIso.symm ≪≫ e ≪≫
    (finiteBaseNativeDescent (k₀ := k₀)).mapIso
      (asIso (CondensedRing.smoothOrientation l
        (Over.mkIdTerminal.from (Over.mk (X ↘ Spec (CommRingCat.of k₀)))) d)).symm⟩

end AlgebraicGeometry.WeilComplex
