/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- Scalar extension preserves every specified Tor interval of a finite-Tor object. -/
theorem finiteScalar_torInterval
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] :
    ∀ (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T) (r s : ℤ),
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1)) K.obj r s →
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l L (m + 1))
          ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj) r s := by
  intro K r s hK
  exact ProEtale.scalarExtension_tor a T K.obj r s hK

end WeilConjectures.ExceptionalFiniteScalar
