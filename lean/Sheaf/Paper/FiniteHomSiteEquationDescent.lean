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

/-- Descent of the naturality, transpose, composition, and coefficient-tower laws.
This is conditional on the geometric tensor squares and descent, and asserts no
new tensor normalization or Hom invertibility.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 7
(blueprint: lem-coef-finite-hom-site-equation-descent).

Proof: on etale-origin objects apply monoidal-square Hom transport. Identify its
left closed adjunction with the specified right tensor-Hom adjunction by the signed
symmetry; both comparisons are transposes of the same evaluation. The inverse site
component occurs in the contravariant input. Cancel the invertible site Hom maps to
carry naturality, all transposes, and internal composition through the square.
For each quotient tower, paste the two squares and use the supplied quotient
coherence to cancel the site components. The assumed etale tower equation then
gives the intrinsic one. For the identity quotient use the mate of the identity
restriction: its unit is coefFiniteHomProUnit, and on the etale side it is the
specified normalizedOriginScalarUnit. Finally choose finite-Tor constructible
etale witnesses of every intrinsic input using the descent hypothesis. Naturality
of the comparisons and the fixed associators conjugates each obtained identity by
these witness isomorphisms. Their inverses cancel, so the resulting equation holds
for the original objects independently of witnesses. Apply the same argument to
every object in a triple for internal composition. -/
theorem finiteHomSiteEquationDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (hdescent : ∀ n : ℕ, CoefFiniteHomDescent l E X n)
    (hsquare : ∀ (n m : ℕ) (h : m ≤ n), CoefFiniteHomSquare l E X h)
    (hmonoidal : ∀ (n m : ℕ) (h : m ≤ n),
      CoefFiniteHomMonoidalSquare
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
            (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
            (finiteHomNu l E X n) (finiteHomNu l E X m)
            (finiteHomEtaleTensor l E X h) (coefFiniteHomProTensor l E X h)
            (finiteHomNuTensor l E X n) (finiteHomNuTensor l E X m)
            (coefFiniteHomSiteIso l E X h))
    (hquotient : ∀ (n m : ℕ) (h : m ≤ n), CoefFiniteHomQuotientCoherence l E X h) :
    ∀ (n m : ℕ) (h : m ≤ n),
      (CoefFiniteHomLawsOn
            (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
            (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
            (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X) →
            CoefFiniteHomLawsOn
              (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
              (coefficientFiniteQuotientDerived l E X h) (coefFiniteHomProTensor l E X h)
              (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
          CoefFiniteHomSuccessive l E X h := by
  sorry

end WeilConjectures
