/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension

/-!
# Uniform torsion cohomology bound for proper geometric fibres

Source: Stacks Project, Tags 0A3V (lemma-morphism-finite-type-bounded-dimension),
00P3 (lemma-dimension-preserved-field-extension), and 0F0V (proposition-cd-affine),
with the blueprint finite-type torsion cohomological-dimension bound, applied in
sec-six-functors-basics/sk-thm-sfb-proper-base-change,
sk-thm-sfb-proper-base-change-finite.proof.md, paragraph (1).
(blueprint: lem-sfb-proper-geometric-fibre-torsion-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper morphism with quasi-compact target has a uniform cohomology bound for
sectionwise torsion abelian sheaves on all its geometric fibres. Each section has its
own nonzero integer annihilator; no common annihilator is part of the hypothesis.
Empty bases and empty fibres are included.

Source: Stacks Project, Tags 0A3V, 00P3 and 0F0V; blueprint proper base change finite,
proof paragraph (1) (blueprint: lem-sfb-proper-geometric-fibre-torsion-bound).

Proof:
1. Properness implies finite type. By lem-fin-finite-type-fibre-dimension-bound,
quasi-compactness of the target gives a natural number e bounding all ordinary fibre
dimensions. Set c = 2e, also when the base is empty.
2. The geometric point gives an extension of the residue field. The iterated base
change identity of def-pc-base-change identifies its geometric fibre with that field
extension of the ordinary fibre. Properness survives base change
(lem-weil-pbc-proper-base-change), and lem-kun-dimension-extension preserves the
dimension. Thus the geometric fibre has dimension at most e.
3. A nonempty geometric fibre has dimension d with 0 <= d <= e, by
def-kun-topological-krull-dimension. Its algebraically closed coefficient field is
separably closed, so lem-sf-separably-closed-torsion-cd gives field torsion dimension
zero. Apply thm-sc-finite-type-torsion-cd to obtain the bound 2d <= 2e, interpreted
by def-sc-etale-torsion-cd using ordinary derived-section cohomology. Sectionwise
torsion implies the local torsion required there by using the maximal covering sieve.
No constructibility or invertibility condition is needed.
4. On an empty fibre, the empty covering forces every abelian sheaf to be zero
(def-weil-pbc-abelian-etale-sheaves). Its zero resolution computes zero cohomology
in every degree (def-weil-pbc-etale-cohomology). This completes all cases. -/
theorem exists_proper_geometricFibre_torsion_cohomology_bound
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] [CompactSpace Y] :
    ∃ c : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (ybar : Spec (.of Ω) ⟶ Y)
      (F : Sheaf (pullback p ybar).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (U : (pullback p ybar).Etaleᵒᵖ) (s : F.obj.obj U),
        ∃ n : ℤ, n ≠ 0 ∧ n • s = 0) →
      ∀ i : ℤ, (c : ℤ) < i →
        Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback p ybar) i).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  sorry

end AlgebraicGeometry
