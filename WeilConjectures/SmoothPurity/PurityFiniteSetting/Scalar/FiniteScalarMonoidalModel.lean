/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat

/-! # A constructed monoidal model for fixed scalar extension

Source: Stacks 07A4 and 0FPT, derived extension of scalars.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Transport the native derived monoidal structure along uniqueness of left adjoints.
This is a construction from the actual scalar adjunctions, without choosing a monoidal
structure from an existence theorem.
Source: Stacks 07A4 and 0FPT
(blueprint: def-pur-finite-scalar-monoidal-model). -/
@[irreducible] def finiteScalarMonoidalModel {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CoreMonoidal := by
  letI : Algebra A B := φ.toAlgebra
  let F := ProEtale.sheafExtendScalars φ T
  letI : F.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  letI : F.leftDerivedFunctor.Monoidal :=
    F.leftDerivedFunctorMonoidal
  let a : F.leftDerivedFunctor ⊣
      ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T :=
    ProEtale.leftDerivedSheafExtendScalarsAdjunction A B T
  let b := Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  exact Functor.Monoidal.coreMonoidalTransport (a.leftAdjointUniq b)

end WeilConjectures.PurityFiniteSetting
