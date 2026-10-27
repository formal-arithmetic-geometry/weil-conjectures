/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/-- Integral compact support preserves the finite-Tor constructible subcategory.
Source: Zheng, Construction 5.25 and Propositions 5.24 and 5.26;
coefficient construction step 3.
Proof: extend by zero and proper direct image on normalized finite systems, then transport
constructibility and a common Tor interval through strict evaluation and derived completion.
(blueprint: lem-sf-integral-support-preservation). -/
theorem integral_support_preservation (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l) :
    ∀ K : finiteTorConstructibleIntegralCategory l E.carrier X,
      finiteTorConstructibleIntegral l E.carrier Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj
          K.obj) := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
