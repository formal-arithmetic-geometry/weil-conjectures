/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleVectorIntegrationArrows
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization

/-! # Canonical equations for tensor integration site comparison
Source: Stacks 099R, 0944 and 0B65; vector-bundle integration
(blueprint: def-pur-vector-tensor-site-equations).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
