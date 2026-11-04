/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.SheafSquareTransport
public import WeilConjectures.WeilSheaf.Native.NativePullTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationSheafTensor

/-! # The native sheaf tensor square under condensed realization -/

@[expose] public section

set_option Elab.async false
set_option trace.profiler true
set_option trace.profiler.threshold 500
set_option diagnostics true
set_option diagnostics.threshold 1000

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The native pullback tensor comparison and the condensed realization tensor comparison
commute with the pullback comparison. -/
def SheafPullTensorSquare (M N : ProEtaleWeilSheaf k₀ l Y) : Prop :=
  PullTensorSquare (upperStar k₀ l g) (condensedRealization k₀ l Z)
    (condensedRealization k₀ l Y)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
    (nativeOpenSheafTensor k₀ l Y) (nativeOpenSheafTensor k₀ l Z)
    (nativePullSheafTensor k₀ l g) (condensedRealizationSheafTensorIso k₀ l Y)
    (condensedRealizationSheafTensorIso k₀ l Z) (condensedRealizationUpperStarIso k₀ l g) M N

end AlgebraicGeometry.ProEtaleWeilSheaf
