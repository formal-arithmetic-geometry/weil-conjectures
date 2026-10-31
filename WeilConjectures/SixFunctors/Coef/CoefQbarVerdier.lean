/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierCore
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierInternalHom
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierExceptional
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierDualizing

/-! # Assembly of common-stage Verdier duality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The complete common-stage Verdier conclusion: the duality, its actual internal
Hom and dualizing object, and the descended exceptional adjunction for every
separated finite-type k-morphism. All data are conclusions, with no ambient adjoint
assumption and no relation imposed on the scheme and coefficient universes.
Source: blueprint thm-coef-qbar-verdier, all statement clauses
(blueprint: thm-coef-qbar-verdier). -/
def CoefQbarVerdierConclusion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] : Prop :=
  ∃ BX : CoefQbarVerdier.Duality D l hl Ω X,
    Nonempty (CoefQbarVerdier.InternalHom D l hl Ω X BX) ∧
    CoefQbarVerdier.Dualizing D l hl Ω X BX ∧
    ∀ {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
      [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f),
      ∃ (BY : CoefQbarVerdier.Duality D l hl Ω Y)
        (A : CoefQbarVerdier.Exceptional D l hl Ω X f c),
        Nonempty (CoefQbarVerdier.InternalHom D l hl Ω Y BY) ∧
        CoefQbarVerdier.Dualizing D l hl Ω Y BY ∧
        Nonempty (CoefQbarVerdier.ExceptionalFormula D l hl Ω X f BX BY c A)

/-- Verdier biduality at algebraically closed coefficients.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-qbar-verdier, statement and proof (blueprint: thm-coef-qbar-verdier).

Proof: core_descent supplies finite-origin duality and evaluation on X.
core_complete derives the three retract equations from naturality, giving the
specified Duality record. Apply internal_hom_descent and dualizing_descent to that
same record. For every f and compactification c, repeat this construction on Y
and apply exceptional_descent to the two fixed dualities. Package the resulting
exceptional system and comparison with the internal-Hom and dualizing conclusions
on Y. The separate source results retain the finite scalar, evaluation, unit and
counit normalizations of the ten-step source argument.
-/
theorem coef_qbar_verdier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    CoefQbarVerdierConclusion D l hl Ω X := by
  obtain ⟨BX, hBX⟩ := CoefQbarVerdier.core_descent D l hl Ω X
  let B := CoefQbarVerdier.completeCore D l hl Ω X BX hBX
  refine ⟨B, CoefQbarVerdier.internal_hom_descent D l hl Ω X B,
    CoefQbarVerdier.dualizing_descent D l hl Ω X B, ?_⟩
  intro Y _ _ _ _ f _ _ _ _ c
  obtain ⟨BY, hBY⟩ := CoefQbarVerdier.core_descent D l hl Ω Y
  let C := CoefQbarVerdier.completeCore D l hl Ω Y BY hBY
  obtain ⟨A, hA⟩ := CoefQbarVerdier.exceptional_descent D l hl Ω X f B C c
  exact ⟨C, A, CoefQbarVerdier.internal_hom_descent D l hl Ω Y C,
    CoefQbarVerdier.dualizing_descent D l hl Ω Y C, hA⟩

end WeilConjectures
