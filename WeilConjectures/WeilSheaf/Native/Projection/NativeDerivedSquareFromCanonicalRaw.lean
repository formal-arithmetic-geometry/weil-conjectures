/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareFromGeometricFunctor
public import WeilConjectures.WeilSheaf.Native.Projection.NativeComplexSquareNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeModelFamilyNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedSquareStatement
public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.NativeTensorTotalInstances
import WeilConjectures.Tactic.ExactModProofs

/-! # Specializing the geometric comparison with an explicit derived square -/

@[expose] public noncomputable section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1000
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

variable (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- Specialize the comparison while keeping the derived square in its explicit form. -/
lemma projection_derived_square_of_canonical_raw
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T)
    (htotal : PullTensorSquareWithComparison
      ((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)) ((condensedRealization k₀ l Z).mapHomologicalComplex (.up ℤ))
      ((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ)) ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).mapHomologicalComplex (.up ℤ))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Y))
      (Functor.uncurry.obj (nativeTensorTotal k₀ l Z)) (nativePullTotalTensor k₀ l g) (condensedRealizationTotalTensorIso k₀ l Y) (condensedRealizationTotalTensorIso k₀ l Z)
      (projection_model_complex_square (upperStar k₀ l g) (condensedRealization k₀ l Z) (condensedRealization k₀ l Y) (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) (condensedRealizationUpperStarIso k₀ l g).symm).symm
      (fun X Y ↦ ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).mapCochainComplexμIso X Y).inv) P T) :
    PullTensorSquareWithComparison (upperStar k₀ l g).mapDerivedCategory
      (condensedRealization k₀ l Z).mapDerivedCategory (condensedRealization k₀ l Y).mapDerivedCategory
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).mapDerivedCategory (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
      (nativePullTensor k₀ l g) (condensedRealizationTensor k₀ l Y) (condensedRealizationTensor k₀ l Z) (Functor.mapDerivedCategorySquareIso (condensedRealizationUpperStarIso k₀ l g).symm).symm
        (fun X Y ↦ ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).mapDerivedCategoryTensorComparison.app X).app Y)
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T) := by
  exact projection_derived_square_of_geometric_functor k₀ l g
    (condensedRealizationUpperStarIso k₀ l g).symm P T hP hT htotal

end AlgebraicGeometry.ProEtaleWeilSheaf
