/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! Finite-origin comparison descent for the common-stage internal Hom.

Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite-origin duality comparisons glue to the common-stage Hom functor.
Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
(blueprint: lem-coef-qbar-verdier-internal-hom-comparison).
Proof: choose a literal compositum for each pair. The finite HomIdentification
comparison is compatible with every scalar transition by the recorded beta and
normalization equations. Eventual equality of representatives therefore gives a
natural isomorphism from the descended dual to `homDual`. -/
theorem internal_hom_comparison_exists (B : Duality D l hl Ω X) :
    ∃ permitted : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
      commonStageHomPairs l Ω X (op K, B.omega),
      Nonempty (B.duality.dual ≅ homDual l Ω X B.omega permitted) := by
  sorry

end WeilConjectures.CoefQbarVerdier
