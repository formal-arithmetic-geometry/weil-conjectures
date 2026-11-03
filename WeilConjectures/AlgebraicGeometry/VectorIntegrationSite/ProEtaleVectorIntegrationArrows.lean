/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleVectorIntegration

/-! # Pro-etale vector integration with local normalization
Source: main-20261015, vector-bundle integration; Stacks 09AF and 099R
(blueprint: def-pur-proetale-vector-integration-arrows).
-/
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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
variable (S : Scheme.{u}) [IsNoetherian S]
variable (r : ℕ)
  (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
variable (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
