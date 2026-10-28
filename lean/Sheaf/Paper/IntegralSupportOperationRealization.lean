/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData

/-! # Integral exceptional operation and compact-support realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- An integral exceptional operation with its compact-support realization exists.
Source: Zheng, Construction 5.25 and Propositions 5.24 and 5.26; coefficient
construction step 3 (blueprint: lem-sf-integral-support-operation-realization).

Proof: construct the normalized reduction/total-limit operation on the complete
finite-Tor categories, transport its system adjunction through the recorded
reconstruction equivalences, and identify its ambient realization with the
proper/open compact-support image. The full finite-Tor inclusions then provide
the required operation and left realization.
-/
theorem exists_integral_support_operation_realization
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l) :
    ∃ A : Operation.{u} l Ω X Y (.integral E),
      Nonempty (LeftRealization.{u} l Ω c (.integral E) A) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
