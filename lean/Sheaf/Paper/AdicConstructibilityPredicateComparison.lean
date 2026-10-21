/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.CondensedQbarLfpLocalTriviality

/-!
# Adic constructibility predicates on Noetherian schemes

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-existence,
`det-existence-restriction.proof.md`, integral and rational cases, and
sec-proetale-coefficients/sk-def-sfb-constructible, clauses 1--2 and final paragraph
(blueprint: lem-sfb-adic-constructibility-predicate-comparison).

The comparison uses the specified condensed multiplication and the existing internal
module predicates. Under the section-action equivalence these are the same module sheaves.
Both bounded predicates live in the ordinary derived category; no completion is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Stratified local finite presentation agrees with finite constant scalar local models
for the three certified adic coefficient rings, including integral torsion modules.
Consequently their bounded constructible object properties in the same ordinary derived
category agree. The two existentially quantified stratifications need not be identical.

Source: blueprint main-20261015, `det-existence-restriction.proof.md`, integral/rational
cases; `sk-def-sfb-constructible/_section.md`, clauses 1--2 and final paragraph
(blueprint: lem-sfb-adic-constructibility-predicate-comparison).

Proof plan (the node's seven steps):
1. Use `def-weil-pbc-internal-abelian-sheaf-module-equivalence`. Its section-action
functor keeps the underlying sheaf, sections and restrictions. Finite free modules and
cokernel presentations therefore agree in the two conventions. The coefficient
identifications and module restrictions are those of `sk-prop-sfb-cartesian-coefficients`.
2. Local Noetherianity gives quasi-separatedness by
`lem-weil-pbc-locally-noetherian-quasi-separated`; together with compactness this selects
the qcqs branch of `sk-def-sfb-constructible`. By
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, descending closed chains stabilize.
For a chain in a stratum, write its terms as intersections with ambient closed sets and
replace the ambient sets by their successive finite intersections. The ambient chain
stabilizes, so every stratum has Noetherian underlying topology as well.
3. A finite constant model gives local finite presentation by
`det-def-sfb-constructible-local-model`. The same stratification then proves
`def-sfb-constructible-module`. This direction includes integral torsion modules.
4. In the integral case, apply `lem-sfb-integral-lfp-constant-model-comparison` on X.
It compares exactly these two predicates and permits a changed finite stratification;
it does not require the finitely presented scalar modules to be torsion-free.
5. For finite field coefficients choose a stratification witnessing
`def-sfb-constructible-module`. On each Noetherian stratum use
`def-sfb-locally-finitely-presented` and `lem-weil-pbc-condensed-lfp-local-triviality` to
obtain a pro-etale cover with finite free restrictions of ranks r. The scalar module E^r
is finitely presented (the presentation from zero suffices), and extension of scalars
identifies its constant model with that finite free restriction.
6. For algebraic-closure coefficients use `lem-weil-pbc-condensed-qbar-lfp-local-triviality`
instead, with precisely the finite-subextension-valued ring of `sk-def-sfb-qlbar-condensed`.
Its scalar ring is the algebraic closure, because a single element lies in a finite
subextension. The scalar free modules of rank r again give the required local models.
7. Apply the module equivalence in every cohomological degree. The two definitions
`sk-def-sfb-bounded-constructible` and `sk-def-sfb-constructible` have the same boundedness
condition, so retain the same finite interval and obtain equality of object properties.
Their full subcategories have the same ambient morphisms. No step requires completeness.
-/
theorem adicConstructibilityPredicateComparison
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance) :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M) ∧
    boundedConstructible (condensedRingObj Λ X) = constantModelBoundedConstructible Λ X := by
  sorry

end AlgebraicGeometry.ProEtale
