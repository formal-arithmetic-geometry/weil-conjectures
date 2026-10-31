/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.EtaleSumOperationExistence
import WeilConjectures.AlgebraicGeometry.EtaleSumSupportComparisonAt

/-! # Exact étale sum calculus on coefficient towers

The étale calculus is constructed independently of any compactification compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The geometric part of the etale sum construction, without any preservation
assertion or finite-level interval assertion.
Source: Stacks 03DI, 03DJ, 03S5 and the latest blueprint Local pairs and Levels.

Proof: On the sequence site, sheafify the sum indexed by lifts through e. Adjacent
coefficient maps retain the lift index. The insertion and fold maps give the ordinary
adjunction and its normalized finite evaluation equations. Ringed localization makes
both functors exact. Apply the adjunction degreewise, then localize it using the exact
composition comparisons: the triangle identities give the unbounded adjunction, and
its unit and counit are the prescribed localized ordinary maps.
For a compactification c, the clopen graph summand and the total-derived direct-image
unit give a map from this derived sum to F_c. Its evaluation is the finite graph map:
ordinary graph uniqueness identifies the ordinary maps, and localization identifies
the derived maps. For a constructible finite-Tor input each finite level admits a
bounded constructible etale origin. Finite graph normalization identifies the map
on that origin with the canonical compact-support comparison, hence makes it an
isomorphism. Joint conservativity of evaluation makes the tower map invertible.
Restrict its inverse to C and conjugate by realization to obtain the displayed
comparison for every c. The extension is determined up to its adjunction-normalized
isomorphism by the fixed right adjoint. Only this universal property and isomorphism-invariant
preservation statements are used downstream; no public definition chooses a functor
from this existence theorem.
(blueprint: lem-v5-etale-sum-support). -/
theorem etale_sum_support_exists
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    {U T : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (e : U ⟶ T) [e.IsOver (Spec (.of k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e] :
    Nonempty (Σ d : EtaleOperation l E b o z e, ∀ c : Compactification e,
      inclusion l E b q U ⋙ F l E b o q c ≅
        inclusion l E b q U ⋙ etaleExtension l E b o q z d) := by
  classical
  obtain ⟨d⟩ := etale_sum_operation_exists l E pchar hp hne k b o x laws q z e
  refine ⟨d, ?_⟩
  intro c
  exact (etale_sum_support_comparison_at l E pchar hp hne k b o x laws q z e d c).some

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
