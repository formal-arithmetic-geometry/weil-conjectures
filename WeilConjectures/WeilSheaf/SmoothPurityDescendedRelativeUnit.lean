/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedIsIso
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedUnitBaseChange
import WeilConjectures.Mathlib.Tactic.ExactModProofs

/-! # Relative proper base change in the actual descended exchange -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Rebase

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {Z Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (p : Z ⟶ Y) [IsProper p.left]
  {Z' : Scheme.{u}} {s t : Z' ⟶ Spec (.of k₂)}
  [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
  [LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]
  (p' : Z' ⟶ Y'.left) [IsProper p']
  (hs : p' ≫ Y'.hom = s) (ht : p' ≫ Y'.hom = t)
  {πZ : Z' ⟶ Z.left} {πY : Y'.left ⟶ Y.left}
  (sq : IsPullback πZ p' p.left πY)

/-- Changing the written structure map of the upper-left corner does not change
invertibility of the specified exceptional base change. -/
lemma isIso_upperShriekBaseChangeOfMap_overMk_congr (h : s = t)
    [IsIso ((upperShriekBaseChangeOfMap l (f := p)
      (f' := Over.homMk (U := Over.mk t) p' ht) sq).app (𝟙_ _))] :
    IsIso ((upperShriekBaseChangeOfMap l (f := p)
      (f' := Over.homMk (U := Over.mk s) p' hs) sq).app (𝟙_ _)) := by
  subst t
  assumption

end Rebase

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The proper unit comparison for the geometric fibre of the chosen compactification
implies invertibility for exactly the exchange used by finite-base descent. -/
theorem isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_of_proper
    [IsIso ((upperShriekBaseChangeOfMap l
      (isPullback_geometricFiberOverMap ((compactificationOverField f).overG
        (f := f)))).app (𝟙_ _))]
    (e : (boundedConstructibleUpperStarOfMap l (X := Y)
      (Y := geometricFiberOver Y) Y.hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (traceGeometricFiberOverMap f)
      (descendedShriekGeometricExchange l f) e) := by
  have : IsIso ((upperShriekBaseChangeOfMap l
      (f := (compactificationOverField f).overG (f := f))
      (f' := ((compactificationOverField f).geometricFiber (Over.w f)).overG
        (f := traceGeometricFiberOverMap f))
      (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
        (compactificationOverField f).g rfl).flip).app (𝟙_ _)) := by
    apply isIso_upperShriekBaseChangeOfMap_overMk_congr l
      ((compactificationOverField f).overG (f := f))
      (Scheme.Hom.geometricFiberMap (compactificationOverField f).g rfl)
      rfl (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _)
      (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
        (compactificationOverField f).g rfl).flip
      (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _)
  dsimp only [descendedShriekGeometricExchange]
  exact isIso_smoothUnitBaseChange_fieldCompactification_of_proper l f
    (traceGeometricFiberOverMap f)
    (compactificationOverField f) ((compactificationOverField f).geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).i
      ((compactificationOverField f).i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
      (compactificationOverField f).g rfl).flip e

end AlgebraicGeometry.ProEtale.CondensedRing
