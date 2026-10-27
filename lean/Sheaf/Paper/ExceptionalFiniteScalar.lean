/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.ExceptionalFiniteScalarMatesData

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The literal finite scalar restriction package exists at every finite-type `k`-scheme.
Source: Stacks 06YY and 09AL; finite scalar construction, steps 1--2
(blueprint: lem-sf-exceptional-finite-scalar-restriction).

The package records preservation of constructibility and the Tor interval, the
equality realization of the restricted ambient tensor functor, and its inherited
commuting shift.  No flatness of the coefficient map is assumed.

Proof in words.  Let `K` be constructible of Tor amplitude in `[r, s]` over `A`.  Since
`T` is of finite type over `k` and `l ≠ p`, `l` is invertible on `T`, so the flat-model
lemma gives a bounded complex `P` of flat constructible `A`-modules in degrees `[r, s]`
representing `K`.  A bounded complex of flat sheaves is K-flat, so `K ⊗^L_A B` is computed
by `P ⊗_A B`, whose terms are flat over `B` (base change of flatness) and constructible
(finite coefficient change preserves constructibility).  Hence `K ⊗^L_A B` is constructible of
Tor amplitude in `[r, s]` over `B` (Tor comparison), which gives `preserves` and
`torInterval`.  The functor is the full-subcategory lift of `ι ⋙ S_a`, so `scalar_eq` holds
by `rfl`; take as `commShift` the shift induced through the fully faithful `ι` from the
ambient derived tensor shift, for which `realizationShift` holds by construction.
Uses: lem-sf-flat-model, lem-pur-derived-change-of-rings, lem-sf-comparison-tor-amplitude.
-/
theorem finiteScalar_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] :
    Nonempty (Scalar l E L n m a T) := by
  sorry


end WeilConjectures.ExceptionalFiniteScalar
