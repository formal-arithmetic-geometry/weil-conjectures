/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteBrown.FiniteBrownAdjointData
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekTriangle
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedOpenCounitSiteTransport
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteBrown
/-- The signed open-cover triangle in the intrinsic finite pro-etale category.
Source: `exists_distinguished_openCover_lowerShriek` and
`unboundedOpenCounitSiteTransport`, proof step 5.
(blueprint: sk-lem-sp-finite-existence).
Proof plan: apply the etale distinguished triangle, transport its three vertices and arrows
through the site comparison and the unbounded counit transport, and use full faithfulness. -/
theorem finiteBrownAdjointExistence_mayerVietoris
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f) [Smooth f]
    (d : ℕ) (_hcd : BaseFieldFiniteCD ell k) (B : BrownData ell n hn k f c) :
    Nonempty (FiniteBrownMayerVietorisData ell n hn k f c B d) := by
  classical
  -- The canonical etale triangle and the unbounded counit-transport identities
  -- determine the three pro-etale arrows.  The full comparison calculation is
  -- retained as this named step for the next proof pass.
  sorry
end AlgebraicGeometry.ProEtale.FiniteBrown
