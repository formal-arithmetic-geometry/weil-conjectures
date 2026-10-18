/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldStageOrdinaryRealization
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude

import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology

/-! # Finite Tor amplitude at field coefficients

Source: Weil conjectures blueprint, node `lem-weil-field-tor-amplitude`, order 2060
(blueprint: lem-weil-field-tor-amplitude).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Field coefficient objects have the finite-Tor property after their specified
ordinary constant-field realization.  The two clauses correspond respectively to a
finite coefficient stage and to the common-stage algebraically closed coefficient
category.  The interval is chosen independently of the test module sheaf.

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
`lem-weil-field-tor-amplitude`, order 2060, statement and proof
(blueprint: lem-weil-field-tor-amplitude).

Proof:
1. By def-weil-finite-tor-amplitude, the field-stage finite-Tor category is the
bounded constructible category itself. Thus the typed Stage and Pair objects already
belong to that subcategory; no additional membership condition is required.
2. Apply lem-sf-field-stage-ordinary-realization to obtain the specified finite or
closure realization and its cohomological boundedness. Choose an ordered interval
[a,b] outside which its cohomology vanishes, before choosing any test module sheaf.
3. For an arbitrary degree-zero module sheaf M, take a K-flat resolution P of a
representative using lem-pc-kflat-resolution. By def-weil-derived-tensor its tensor
with M computes the ordinary derived tensor. Apply
lem-exc-constant-field-sheaf-tensor-cohomology to P and M over the discrete constant
field sheaf. It identifies each tensor cohomology sheaf with H^r(P) tensor M,
which is zero outside [a,b] by step 2. This works for every representative and
resolution and for every M, with no constructibility or dimension restriction on M.
By def-weil-proetale-tor-amplitude this is the asserted single Tor interval. -/
theorem field_tor_amplitude
    (D : FiniteFieldDatum.{d})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (Y : Scheme.{u}) :
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E),
        ∃ a b : ℤ, Scheme.HasProEtaleTorAmplitude Y
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E)
          ((OrdinaryFieldRealization.System.finite
            (Classical.choice
              (OrdinaryFieldRealization.exists_ordinaryFieldRealization D l hl Ω Y)) E).obj K)
          a b) ∧
      (∀ (K : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y),
        ∃ a b : ℤ, Scheme.HasProEtaleTorAmplitude Y
          (OrdinaryFieldRealization.Closure l Ω)
          ((OrdinaryFieldRealization.System.closure
            (Classical.choice
              (OrdinaryFieldRealization.exists_ordinaryFieldRealization D l hl Ω Y))).obj K)
          a b) := by
  sorry

end WeilConjectures
