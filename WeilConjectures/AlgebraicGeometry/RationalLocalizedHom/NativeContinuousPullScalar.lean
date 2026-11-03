/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom.NativeContinuousScalarAction
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Native continuous coefficient scalars

Source: sk-prop-sp-rational-adjunction.proof.md, constant-scalar linearity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalLocalizedHom

attribute [local instance 2000] CategoryTheory.Linear.homModule

set_option maxHeartbeats 1000000 in
-- Elaborate the coefficient linear structures and native derived pullback together.
/-- Native derived inverse image preserves the canonical continuous scalar action.
Source: sk-prop-sp-rational-adjunction.proof.md, paragraph (1), linearity.
Proof: nativeContinuousScalarAction identifies canonical Hom scalars with constant
sections pulled back from the coefficient point. The ordinary condensed module
pullback is linear over the global sections at that point. Restrict that scalar
ring along constant functions, checking the scalar multiples of identities.
The native left derived functor preserves those multiples by its K-flat scalar
lemma, and hence is linear. Rewrite its source and target Hom actions through the
comparison. This works on the unbounded categories, including zero rings, zero
complexes and empty schemes.
(blueprint: lem-sp-native-continuous-pull-scalar). -/
theorem nativePull_map_smul
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TotallyDisconnectedSpace A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y))}
    (h : K ⟶ L) (a : A) :
    let P := (CondensedRing.upperStar (Profinite.continuousMapRingObj A) f).leftDerivedFunctor
    P.map (@SMul.smul A (K ⟶ L) (homModule Y A K L).toSMul a h) =
      @SMul.smul A (P.obj K ⟶ P.obj L)
        (homModule X A (P.obj K) (P.obj L)).toSMul a (P.map h) := by
  let px := (MonObj.Γ.mapFunctor (upperStarFromPoint X)
    (R := Profinite.continuousMapRingObj A)).comp
      (Profinite.continuousMapConstRingHom A)
  let py := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)
    (R := Profinite.continuousMapRingObj A)).comp
      (Profinite.continuousMapConstRingHom A)
  letI := Mod.linearOfRingHom px
  letI := Mod.linearOfRingHom py
  let F := CondensedRing.upperStar (Profinite.continuousMapRingObj A) f
  have hp (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y)) (b : A) :
      F.map ((Mod.smulNatTrans (py b).hom).app M) =
        (Mod.smulNatTrans (px b).hom).app (F.obj M) := by
    letI := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint X)
      (R := Profinite.continuousMapRingObj A))
    letI := Mod.linearOfRingHom (MonObj.Γ.mapFunctor (upperStarFromPoint Y)
      (R := Profinite.continuousMapRingObj A))
    letI := condensedModulePullback_linear (Profinite.continuousMapRingObj A) f
    have hb := Functor.map_smul F (Profinite.continuousMapConstRingHom A b) (𝟙 M)
    rw [CategoryTheory.Functor.map_id, Mod.linearOfRingHom_smul_id,
      Mod.linearOfRingHom_smul_id] at hb
    exact hb
  haveI : F.Linear A := (Functor.linear_iff A F).2 fun M b ↦ by
    rw [Mod.linearOfRingHom_smul_id, Mod.linearOfRingHom_smul_id]
    exact hp M b
  haveI : F.leftDerivedFunctor.Linear A :=
    (Functor.linear_iff A F.leftDerivedFunctor).2 fun M b ↦ by
      simpa only [RingHom.id_apply] using
        Functor.leftDerivedFunctor_map_smul_id (RingHom.id A) F
          (fun N c ↦ by rw [Functor.map_smul, CategoryTheory.Functor.map_id]; rfl) M b
  change F.leftDerivedFunctor.map _ = _
  rw [nativeContinuousScalarAction Y A h a,
    nativeContinuousScalarAction X A (F.leftDerivedFunctor.map h) a]
  exact Functor.map_smul F.leftDerivedFunctor a h

end AlgebraicGeometry.ProEtale.RationalLocalizedHom
