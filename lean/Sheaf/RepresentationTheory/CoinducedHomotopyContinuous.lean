/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker F1
-/
import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Continuity of the coinduced contracting operator

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG,
label section-continuous-group-cohomology, final profinite comparison.
The explicit contraction is an agent-written proof ingredient
(blueprint: lem-exc-coinduced-homotopy-continuous).
-/

universe u v w

namespace Rep

/-- The formula inserting `x` as the first group variable and evaluating the resulting
function at the identity defines a linear map between continuous cochains.
`LocallyConstant G M.obj.V` is the coinduced function module of
`exists_coinduced_discrete_embedding`. Nested locally constant maps encode the discrete
topology on that whole module, rather than a compact-open topology.
The index `n + 1` ranges over all positive degrees, including degree one at `n = 0`.

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG,
label section-continuous-group-cohomology, final profinite comparison
(blueprint: lem-exc-coinduced-homotopy-continuous).

Proof: (1) The setup of `lem-exc-discrete-modules-abelian` and
`lem-exc-coinduced-discrete-embedding` supplies the discrete module and the pointwise
module structure on its continuous function module with right translation.
Evaluation at one and substitution in the first variable are linear pointwise.
(2) For fixed remaining variables, the function of `x` obtained by this formula is
continuous into the discrete module: insertion of `x` is continuous, and evaluation
at one is continuous from the discrete function module. For any fixed tuple of
remaining variables, joint continuity supplies product neighborhoods where the
value is constant. Compactness of `G` gives a finite cover in the `x` variable.
Intersect the finitely many neighborhoods of the remaining tuple. On this
intersection all `x` values agree with the original function, so the resulting
function-valued map is locally constant into the discrete coinduced module.
Thus it is a continuous cochain; pointwise linearity gives the asserted linear map. -/
theorem exists_coinduced_continuous_contraction
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (M : DiscreteContinuousRep.{v, u, w} A G) (n : ℕ) :
    ∃ h : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V) →ₗ[A]
        LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V),
      ∀ (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
        (g : Fin n → G) (x : G),
        h F g x = F (Fin.cons x g) 1 := by
  sorry

end Rep
