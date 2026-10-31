/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalModel

/-! # The canonical comparison of fixed and native derived scalar adjoints -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The canonical comparison from the fixed scalar adjoint to ordinary derived scalar
extension. Source: Stacks 06YY and 07A4.
(blueprint: def-pur-finite-scalar-derived-comparison).
It is constructed as the inverse of leftAdjointUniq for the two actual adjunctions. -/
@[irreducible] noncomputable def finiteScalarDerivedComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    letI : Algebra A B := φ.toAlgebra
    letI : (ProEtale.sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
      ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
    ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T ≅
      (ProEtale.sheafExtendScalars φ T).leftDerivedFunctor := by
  letI : Algebra A B := φ.toAlgebra
  let F := ProEtale.sheafExtendScalars φ T
  letI : F.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  let a : F.leftDerivedFunctor ⊣
      ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T :=
    ProEtale.leftDerivedSheafExtendScalarsAdjunction A B T
  let b : ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T ⊣
      ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T :=
    Adjunction.ofIsRightAdjoint
      (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  exact (a.leftAdjointUniq b).symm

end WeilConjectures.PurityFiniteSetting
