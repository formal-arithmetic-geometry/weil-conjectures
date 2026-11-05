/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.DerivedSquareFromModelFamilies
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareOfRepresentatives
public import WeilConjectures.WeilSheaf.Native.Projection.TotalSquareToModel
public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelFamilyNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.TensorSquare
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.WeilSheaf.Native.Projection.StrictProof

/-! # Localization of the native pullback tensor square -/

@[expose] public noncomputable section

set_option Elab.async false
-- Keep dependent model data as lets; letToHave expands their native isomorphism types.
set_option cleanup.letToHave false

-- Use the coefficient-category instance fixed by the native tensor construction.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

attribute [local instance] projection_hasSmallColimits projection_hasTensor
  projection_nativeHasTotal projection_tensorLeftPreservesInitial
  projection_tensorRightPreservesInitial projection_hasGoodTensor12
  projection_hasGoodTensor23 projection_hasTensor4Ext

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

variable (htotal : ∀ P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ,
  TotalPullTensorSquare k₀ l g P T)

set_option maxHeartbeats 1000000 in
-- The native model interfaces previously exhausted 800000 elaboration heartbeats.
include htotal in
/-- On K-flat representatives, the native tensor square is the localization of the
square of total complexes. -/
lemma condensedRealizationTensor_pull_square_Q_of_total
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T) :
    DerivedPullTensorSquare k₀ l g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  projection_strict
    let L := upperStar k₀ l g
    let V := condensedRealization k₀ l Z
    let F := condensedRealization k₀ l Y
    let R := CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))
    exact projection_derived_square_of_model_families L V F R
      (condensedRealizationUpperStarIso k₀ l g).symm
      (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      (condensedRealizationTensor k₀ l Y) (condensedRealizationTensor k₀ l Z)
      (nativePullTensor k₀ l g)
      (nativeTensorTotal k₀ l Y) (nativeTensorTotal k₀ l Z)
      (NativeIsKFlat k₀ l Y) (NativeIsKFlat k₀ l Z)
      (nativeIsKFlat_mapHomologicalComplex_upperStar_obj k₀ l g)
      (nativeOpenTensorModel k₀ l Y) (nativeOpenTensorModel k₀ l Z)
      (nativePullTotalTensor k₀ l g) (condensedRealizationTotalTensorIso k₀ l Y)
      (condensedRealizationTotalTensorIso k₀ l Z)
      (by
        have hn := projection_nativePullTensor_normalization k₀ l g
        dsimp only [ProjectionRestrictionTensorNormalization] at hn
        dsimp only [L, nativeOpenPull]
        set_option pp.maxDepth 8 in
          run_tac Lean.Elab.Tactic.withMainContext do
            let pf ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hn) none
            let H ← Lean.instantiateMVars (← Lean.Meta.inferType pf)
            let G ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
            let mut pending := #[(H, G)]
            let mut seen : Std.HashSet (Lean.Expr × Lean.Expr) := {}
            let mut differences := 0
            while !pending.isEmpty && differences < 20 do
              let (a, b) := pending.back!
              pending := pending.pop
              let a := a.consumeMData
              let b := b.consumeMData
              if a == b || seen.contains (a, b) then continue
              seen := seen.insert (a, b)
              if !a.hasLooseBVars && (← Lean.Meta.isProof a) then continue
              if a.isApp && b.isApp && a.getAppFn == b.getAppFn &&
                  a.getAppNumArgs == b.getAppNumArgs then
                pending := pending ++ (a.getAppArgs.zip b.getAppArgs)
              else
                match a, b with
                | .lam _ ta ba _, .lam _ tb bb _ =>
                    pending := pending ++ #[(ta, tb), (ba, bb)]
                | .forallE _ ta ba _, .forallE _ tb bb _ =>
                    pending := pending ++ #[(ta, tb), (ba, bb)]
                | .proj _ i sa, .proj _ j sb =>
                    if i == j then pending := pending.push (sa, sb)
                    else
                      differences := differences + 1
                      Lean.logInfo m!"K5 data difference: {a}\nversus {b}"
                | _, _ =>
                    differences := differences + 1
                    Lean.logInfo m!"K5 data difference: {a}\nversus {b}"
            (throwError "K5 diagnostic: {differences} non-proof differences" :
              Lean.Elab.Tactic.TacticM Unit))
      (by exact projection_native_realization_model_normalization k₀ l Y)
      (by exact projection_native_realization_model_normalization k₀ l Z)
      (fun A B ↦ (R.mapCochainComplexμIso A B).symm)
      (fun A B ↦ (R.mapDerivedCategoryTensorComparison.app A).app B)
      (by exact R.projection_ordinary_model_normalization)
      P T hP hT
      (by exact htotal P T)

include htotal in
/-- The native pullback tensor square on arbitrary derived objects, extended from K-flat
representatives by naturality. -/
lemma condensedRealizationTensor_pull_square_of_total
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    DerivedPullTensorSquare k₀ l g M N := by
  exact projection_derived_square_of_representatives k₀ l g
    (condensedRealizationTensor_pull_square_Q_of_total k₀ l g htotal) M N

end AlgebraicGeometry.ProEtaleWeilSheaf
