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

/-- The finite chart and coefficient-transfer fields of proof step 3.
Source: `det-sp-finite-existence-chart` (G10 of `sk-lem-geo-affine-local`),
`sk-prop-sp-et-proet`, and the affine trace normalization declarations.
(blueprint: sk-lem-sp-finite-existence).

Proof plan: verify the Noetherian and separated finite-type chart hypotheses, apply the
finite etale chart comparison, transport it across the finite etale/pro-etale equivalence,
and use the ordered affine trace counit. The same construction supplies support preservation,
comparison equivalence, projection normalization, and local chart representability. -/
theorem finiteBrownAdjointExistence_chartCore
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f) [Smooth f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (_hcd : BaseFieldFiniteCD ell k)
    (B : BrownData ell n hn k f c) :
    Nonempty (FiniteBrownChartData ell n hn k f c B d) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteBrown
