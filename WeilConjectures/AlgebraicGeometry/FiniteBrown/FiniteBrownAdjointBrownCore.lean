/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteBrown.FiniteBrownAdjointData

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteBrown

/-- Finite-cd Brown restriction and finite coefficient/site transfer.
Source: `sk-prop-sf-existence` and `sk-prop-sf-rf-shriek-preservation`.
(blueprint: sk-lem-sp-finite-existence).

Proof plan: construct the localizing Brown adjunction over the finite-cd field, restrict it
along the finite coefficient comparison, and transport its counit and representing Hom
bijections to the intrinsic finite ctf categories. The finite coefficient comparison is an
 equivalence, so the resulting right adjoint and counit are determined up to the equality
used by `BrownData`. The zero object and the empty test category are handled by the same
restricted adjunction; no finite-field or algebraic-closure hypothesis is introduced. -/
theorem finiteBrownAdjointExistence_brownCore
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f) [Smooth f]
    (_hcd : BaseFieldFiniteCD ell k) :
    Nonempty (BrownData ell n hn k f c) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteBrown
