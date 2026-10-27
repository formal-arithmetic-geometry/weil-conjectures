/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! Universal property transport for the common-stage internal Hom.

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

/-- The finite evaluation transpose descends along a chosen comparison.
Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: lem-coef-qbar-verdier-internal-hom).
(blueprint: lem-coef-qbar-verdier-internal-hom-universal).
Proof: represent both arguments and a morphism at a common compositum stage.
`finite_evaluation_transpose_bijective` gives inverse maps there. The scalar
comparison and the normalized evaluation square preserve eventual equality, so
these inverse maps descend to the common-stage Hom groups. -/
theorem internal_hom_universal_of_comparison
    (B : Duality D l hl Ω X)
    (permitted : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
      commonStageHomPairs l Ω X (op K, B.omega))
    (_comparison : B.duality.dual ≅ homDual l Ω X B.omega permitted)
    (hproperties : DualityProperties D l hl Ω X B.val) :
    ∀ (K P : generalAlgebraicallyClosedConstructibleCategory l Ω X),
      Function.Bijective (fun h : P ⟶ B.duality.dual.obj (op K) ↦
        (CoefQbarTensor D l hl Ω X).map (Prod.mkHom (𝟙 K) h) ≫ B.evaluation K) := by
  sorry

end WeilConjectures.CoefQbarVerdier
