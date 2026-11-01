/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierCore
public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierInternalHom
public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierExceptional
public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierDualizing

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Current common-stage Qbar Verdier conclusion used by this item. -/
def CurrentCoefQbarVerdierConclusion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
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

/-- Algebraically closed Qbar coefficient-stage Verdier biduality.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
 sk-thm-sfb-qlbar-two-colimit/sk-thm-sfb-qlbar-two-colimit.proof.md`, the
current common-stage coefficient argument.  The proof is the finite-origin
core, internal-Hom and exceptional descent, with evaluation compatibility.
(blueprint: lem-pd-constructible-sheaf-biduality-qbar) -/
theorem qbar_stage_biduality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    CurrentCoefQbarVerdierConclusion D l hl Ω X := by
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
