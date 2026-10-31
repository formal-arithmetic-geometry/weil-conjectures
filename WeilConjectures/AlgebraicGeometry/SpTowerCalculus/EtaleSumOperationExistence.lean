/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # Existence of normalized étale sum operations

The ordinary sheafified lift-sum construction is transported to the recorded strict
coefficient-tower coordinates.  The transport retains the finite evaluation adjunctions
and the localized derived adjunction required by `EtaleOperation`.
(blueprint: lem-v5-etale-sum-operation-existence)
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

/-- The normalized exact étale operation exists before compact-support comparison.

Source: Stacks 03DI--03DJ and 03S5; blueprint Local pairs and Levels.
Proof: identify the pro-étale site over `U` with the localization of the site over `T`.
Sheafify the direct sum over lifts through `e`, and transport the resulting adjunction
along the section-preserving realization coordinates.  Exactness is componentwise;
localization preserves the units, counits and finite coefficient adjunctions.  Descending
the ordinary adjunction degreewise to complexes and then localizing gives the required
unbounded derived adjunction and its termwise formulas.
(blueprint: lem-v5-etale-sum-operation-existence). -/
theorem etale_sum_operation_exists
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
    Nonempty (EtaleOperation l E b o z e) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
