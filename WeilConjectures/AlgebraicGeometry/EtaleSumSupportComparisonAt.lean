/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekInterfaces

/-! # One-compactification comparison for étale sum operations

Adjunction normalization makes the graph map independent of the chosen presentation.
The finite graph calculation and localization then give the compact-support comparison
for one compactification at a time.
(blueprint: lem-v5-etale-sum-support-comparison-at)
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

/-- A normalized étale operation has the compact-support comparison for one
compactification.  The statement is pointwise in the compactification, so the family
in the parent theorem is assembled by dependent choice.

Source: Stacks 0F4L, 0GKM and 03S5; blueprint Local pairs and Levels.
Proof: form the unique graph map from the sheafified lift summands to
`Rp_*j_!`, apply the total right-derived direct-image unit, and transport it through
realization.  On every finite constructible origin its evaluation is the canonical
finite compact-support comparison, hence invertible.  Evaluation is jointly
conservative, so the transported map is invertible and its inverse is the displayed
isomorphism.
(blueprint: lem-v5-etale-sum-support-comparison-at). -/
theorem etale_sum_support_comparison_at
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
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (d : EtaleOperation l E b o z e) (c : Compactification e) :
    Nonempty (inclusion l E b q U ⋙ F l E b o q c ≅
      inclusion l E b q U ⋙ etaleExtension l E b o q z d) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
