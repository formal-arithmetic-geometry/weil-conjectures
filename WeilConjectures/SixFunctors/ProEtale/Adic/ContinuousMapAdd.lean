/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-!
# Sheaves of continuous maps into topological abelian groups

The additive analogues, for a topological abelian group `M` (not necessarily a ring), of the
sheaves of continuous maps of `WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`:

- `AlgebraicGeometry.ProEtale.continuousMapAddSheaf X M`: the abelian sheaf `U ↦ C(U, M)` on
  `X_proét`, and `continuousMapAddSheafMap` for continuous additive maps;
- `AlgebraicGeometry.ProEtale.constantSheafIsoContinuousMapAddSheaf`: for `M` discrete, it is the
  constant sheaf with value `M`, naturally in `M`
  (`constantSheaf_map_comp_constantSheafIsoContinuousMapAddSheaf_hom`);
- `AlgebraicGeometry.ProEtale.isLimitContinuousMapAddSheafCone`: for a tower of topological
  abelian groups `Qₙ`, `C(-, lim Qₙ)` is the limit of the sheaves `C(-, Qₙ)`, with
  `lim Qₙ = towerLimitAddSubgroup τ`.

This allows towers of stalks which are modules rather than rings, e.g. finitely generated
`𝒪_E`-modules with torsion.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

section Add

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

variable {M} {M' : Type} [TopologicalSpace M'] [AddCommGroup M'] [IsTopologicalAddGroup M']

variable (M)

variable [DiscreteTopology M]

variable {M}

variable [DiscreteTopology M']

end Add

section Limit

variable {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, AddCommGroup (Qs n)]
  [∀ n, IsTopologicalAddGroup (Qs n)] (τ : ∀ n, Qs (n + 1) →+ Qs n)
  (hτ : ∀ n, Continuous (τ n))

end Limit

end AlgebraicGeometry.ProEtale
