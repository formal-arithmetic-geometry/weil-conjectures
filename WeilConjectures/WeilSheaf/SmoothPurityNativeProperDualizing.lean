/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeProperTrace
public import WeilConjectures.WeilSheaf.SmoothPurityProperPointTrace
public import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent

/-!
# Native descent of the proper exceptional unit

The exceptional unit of a proper structural morphism is the native realization
of the finite-base exceptional unit. The comparison is obtained from the actual
descended trace, so it respects the Weil datum.
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
  (a : X ⟶ Spec (CommRingCat.of k₀))
  [a.IsOver (Spec (CommRingCat.of k₀))] [IsProper a]

local instance : Fact (ringChar k₀).Prime := ⟨CharP.prime_ringChar k₀⟩
local instance : LocallyOfFiniteType (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))
local instance : QuasiCompact (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))
local instance : IsSeparated (Over.mk (X ↘ Spec (CommRingCat.of k₀))).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))
local instance : IsProper
    (properTraceBaseMap a).left :=
  ‹IsProper a›
local instance : IsProper
    (CondensedRing.traceGeometricFiberOverMap
      (properTraceBaseMap a)).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
    a (comp_over a _) inferInstance

/-- A right adjoint to proper direct image sends the descended finite-base unit
to the descended finite-base exceptional unit. -/
theorem nonempty_rightAdjoint_finiteBaseNativeDescent_unit_iso
    {J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) a ⊣ J) :
    Nonempty (J.obj ((finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj (𝟙_ _)) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj
        ((CondensedRing.boundedConstructibleUpperShriek l
          (properTraceBaseMap a)).obj (𝟙_ _))) := by
  let P := (CondensedRing.boundedConstructibleUpperShriek l (properTraceBaseMap a)).obj
    (𝟙_ _)
  let T := (finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj P
  let U := (finiteBaseNativeDescent (k₀ := k₀) (l := l)
    (X := Spec (CommRingCat.of k₀))).obj (𝟙_ _)
  let eT := (finiteBaseNativeDescentComparison (k₀ := k₀) (l := l)).app P
  let eU := (finiteBaseNativeDescentComparison (k₀ := k₀) (l := l)
    (X := Spec (CommRingCat.of k₀))).app (𝟙_ _)
  have := CondensedRing.isIso_upperShriekBaseChange_geometricFiber_unit l
    (properTraceBaseMap a)
  have hi := isIso_homEquiv_nativeProperTrace_of_isIso a (𝟙 P) T U eT eU adj
  exact ⟨(asIso (adj.homEquiv T U (nativeProperTrace a (𝟙 P) T U eT eU))).symm⟩

/-- The proper exceptional unit is the native descent of the ordinary dualizing
complex over the finite field. -/
theorem nonempty_rightAdjoint_finiteBaseNativeDescent_dualizing_iso
    {J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerStar (k₀ := k₀) (l := l) a ⊣ J) :
    Nonempty (J.obj ((finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj (𝟙_ _)) ≅
      (finiteBaseNativeDescent (k₀ := k₀) (l := l)).obj
        (CondensedRing.dualizingComplex l (Over.mk (X ↘ Spec (CommRingCat.of k₀))))) := by
  obtain ⟨e⟩ := nonempty_rightAdjoint_finiteBaseNativeDescent_unit_iso a adj
  exact ⟨e ≪≫ (finiteBaseNativeDescent (k₀ := k₀) (l := l)).mapIso
    ((CondensedRing.boundedConstructibleUpperShriek l (properTraceBaseMap a)).mapIso
      (CondensedRing.dualizingComplexPointIso l k₀).symm ≪≫
      CondensedRing.upperShriekDualizingComplexIso l (properTraceBaseMap a))⟩

end AlgebraicGeometry.WeilComplex
