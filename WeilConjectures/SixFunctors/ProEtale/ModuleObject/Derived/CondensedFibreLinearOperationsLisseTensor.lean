/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel

/-!
# Lisse duals and tensors for condensed coefficients

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-deligne-laumon-a1/
sec-purity-of-the-lisse-part-of-the-fourier-transform/sk-p-dl-a1-some-weight/
lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-lisse-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Canonical comparison from the derived tensor of two degree-zero modules to the
single complex of their ordinary tensor.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations-lisse-tensor). -/
noncomputable def lisseTensorDerivedComparison
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (F L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj L ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        (MonoidalCategory.tensorObj F L) :=
  (tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L)).hom ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor _ 0).obj F)
      ((CochainComplex.singleFunctor _ 0).obj L) ≫
    DerivedCategory.Q.map (DerivedCategory.moduleCup_singleTensorIso F L).hom ≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
      (MonoidalCategory.tensorObj F L)).inv

attribute [local irreducible] upperStar upperStarComp upperStarFromPoint

end AlgebraicGeometry.ProEtale.CondensedRing
