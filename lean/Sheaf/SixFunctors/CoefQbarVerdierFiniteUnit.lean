/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! Unit component of normalized finite Verdier coherence.

Source: thm-coef-qbar-verdier, identity-extension clause.
(blueprint: lem-coef-qbar-verdier-finite-unit-equation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage unitor)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The identity-stage component equation for a finite Verdier datum.
Source: thm-coef-qbar-verdier, final coefficient-transport paragraph;
(blueprint: lem-coef-qbar-verdier-finite-unit-equation).

Proof: identify the identity coefficient inclusion with the identity field map. Apply
RationalVerdier.extension_unit to the normalized rational extension. Its normalized
integral component is exactly the prescribed stage unitor, by the uniqueness theorem
for the canonical scalar unit and the coefficient-inclusion identity law. Transport
along the resulting equality and evaluate at the given stage object. This argument
also covers repeated fields, zero objects, and the empty scheme. -/
theorem finite_unit_equation (F : Finite D l hl Ω X) :
    ∀ (E : Index l Ω) (K : Stage l Ω X E),
    (F.beta E E le_rfl).hom.app (op K) =
      (unitor l Ω X E).hom.app ((F.datum E).dual.obj (op K)) ≫
        (F.datum E).dual.map ((unitor l Ω X E).hom.app K).op := by sorry

end WeilConjectures.CoefQbarVerdier
