/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.CoefFiniteHomSiteDescentData

/-! # A component of finite Hom site descent

Source: blueprint `lem-coef-finite-hom-site-descent`, final site comparison argument.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The specified evaluation comparison into the intrinsic category is invertible
on a finite-Tor constructible first input and bounded constructible second input.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 5; finite-duality
site comparison (blueprint: lem-coef-finite-hom-site-hom-invertible).

Proof: finite_duality_site_comparison gives invertibility of the evaluation-defined
comparison for sheaves of modules over the constant coefficient ring. Transport its
target across the existing intrinsic realization/restriction equivalence. The
normalization of finiteHomNuTensor identifies its tensorator with pullback of the
ordinary tensor comparison on flat-term K-flat representatives. The normalized
etale and intrinsic closed structures identify both counits with their ordinary
evaluations on those representatives. Uniqueness of the target tensor-Hom transpose
therefore identifies the transported comparison with finiteHomSiteHom. Transport
of an isomorphism across the equivalence proves invertibility of this actual map.
The second input only requires bounded constructibility. -/
theorem finiteHomSiteHomInvertible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ (n : ℕ) (K M : finiteHomEtale l E X n),
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      coefFiniteHomEtaleConstructible l E X n M →
      IsIso (finiteHomSiteHom l E X n K M) := by
  sorry

end WeilConjectures
