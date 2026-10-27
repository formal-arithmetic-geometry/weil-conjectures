/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData
import Sheaf.DeligneLaumon.OrdinarySectionScalarComparison
import Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily
import Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence
import Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices

/-! # Normalized continuous coefficients and stratified integral lattices -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

/-- Constructible continuous modules admit normalized integral lattices on a finite reduced
refinement, over the original coefficient field, with their genuine internal inclusions.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph, Proposition 6.8.4,
Remark 6.8.15; blueprint thm-zl-real-mixed-by-curves paragraph 6
(blueprint: lem-zl-continuous-constructible-stratified-lattices).

Proof plan, following the node's seven steps:
1. Finite type over the noetherian field makes every base and locally closed stratum
noetherian and quasi-compact. Immersions and their reductions remain separated finite type.
2. The extended absolute value is ultrametric. Clopen balls separate points of E and A.
The canonical condensed charts are therefore ring isomorphisms. Compose the integral chart
with continuousCoefficientCompletion: every positive projection is reduction. The rational
chart is its unique localization, so the inclusion square commutes.
3. Chart scheme naturality and continuous coefficient pullback composition identify all
locally closed restrictions. On finite extensions compare compatible quotient powers,
then use uniqueness of limits and localization for the extension squares.
4. sectionModuleEquivalence retains section groups, restrictions and actions. Relative
tensor products impose the same balanced relations, so the scalar comparison is the identity
on pure tensors. Exact inverse image preserves these relations and the submodule inclusions.
5. The encoding local-freeness criterion identifies lisse modules with locally finite free
sectionwise modules, without constant-rank or nonempty-cover conditions.
6. On each member of the supplied lisse partition apply sk-lem-stratified-lattice and take
the finite union of its refinements. Encode each genuine internal inclusion. The embedded
lattice comparison identifies its induced localization with ordinary scalar extension.
7. Pull every lattice back to the reduction, using Stacks 054M. Exact inverse image preserves
its monomorphism, local freeness and inclusion-induced localization. The same calculation
applies to every further locally closed immersion. Empty partitions and zero lattices are
included. No lattice is glued across the strata. -/
theorem continuous_constructible_stratified_lattices
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p) :
    Nonempty (Family D l) := by
  classical
  let c : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], CoefficientFamily l E :=
    fun E _ _ _ ↦ Classical.choice (normalized_continuous_coefficient_family l E)
  obtain ⟨g⟩ := continuous_coefficient_geometric_coherence D l c
  refine ⟨{ ordinary_scalars := ordinary_section_scalar_comparison
            coefficients := c
            restriction := g.restriction
            composition := g.composition
            fieldChange := g.fieldChange
            field_restriction := g.field_restriction
            field_composition := g.field_composition
            strata := ?_ }⟩
  intro E _ _ _ X F S hS
  exact normalized_stratified_embedded_lattices D l _hl E (c E) X F S hS

end WeilConjectures.StratifiedContinuousLattices

