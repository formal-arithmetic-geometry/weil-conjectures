## What changed

The general theorem is reduced to the ordinary constant-module realization and the
normalized tensor-square descent. The remaining argument is proved directly:
exactness follows by reflection along the underlying-sheaf and scalar-restriction
functors; the left comparison is the canonical localized ordinary isomorphism;
the right comparison is its adjunction mate. The mate normalization gives the
right localization square and the full derived Hom equation. Identities give the
unit and counit equations. The projection square follows from the existing abstract
projection-mate theorem. Restricting the unbounded adjunction along the fully faithful
bounded-below inclusions proves the plus comparison, including both counit equations.

The existing localization definitions are factored through generic predicates in
`ConstantModuleDerivedComparisonData`; the equations and existing signatures are
preserved. The bounded-below data consumer uses the same local additive-instance selection.
The change record is
`coord/changes/A6-constant-module-localization-conditions.md`. No source-library file changes.
The removed direct imports are available through the retained data interfaces
except for the projection-mate import, which is replaced by the abstract theorem
used in this proof. There are no current Lean importers of this item module to adapt.

Validation: the four delivery sources and the unchanged bounded-below data consumer
compile together through `lcompile.py`. The final matched set compiled the main proof in 53.8 seconds, and the
final single-file check passed in 53.9 seconds. Both original theorem
signatures and the complete EtaleIdentification definition were compared with the
shared source and are unchanged. Every remaining hole and its node is listed below.

The two new modules isolate different source arguments, ordinary realization and
K-flat tensor descent. Neither is the original theorem under another name: they
contain no derived direct-image comparison, derived Hom equation, projection square,
or bounded-below assertion. The etale-specialization theorem is unchanged.

## Proved and sorry left

Closed in the item:
`CategoryTheory.ConstantModuleDerivedProjection.constant_module_derived_projection_identification`
by a reduction to two proper mathematical parts. This is a decomposition, not a net
hole reduction.

The item's other original hole remains:
`CategoryTheory.ConstantModuleDerivedProjection.etale_constant_module_derived_projection_identification`
(node `lem-sfb-constant-module-derived-projection-identification`).

Added holes:
`CategoryTheory.ConstantModuleDerivedProjection.constant_module_ordinary_realization`
(node `lem-sfb-constant-module-ordinary-realization`) and
`CategoryTheory.ConstantModuleDerivedProjection.constant_module_tensor_square_descent`
(node `lem-sfb-constant-module-tensor-square-descent`).

Thus one of the two original holes is reduced, two are split off, and three holes
remain in the delivery. There are no holes in definitions or private helpers.

## No longer needed

Direct imports removed (some remain transitively available through the data interfaces):

- `Sheaf.Paper.ProjectionMateExact`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.CategoryTheory.ConstantScalarGeometricAdjunctions`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.RingedEquivalenceResolvingTensorDescent`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`

The direct K-injective Hom-chain and plus representative route is replaced by the
exact derived mate and fully faithful adjunction restriction. Accordingly these
original proof dependencies are not needed by the assembly:
`lem-weil-pbc-exact-functor-derived-functor`,
`lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-derived-exact-equivalence-squares`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`,
`lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-dplus-injective-representative`, and
`lem-weil-pbc-right-derived-plus-injective`.
The direct use of `lem-weil-pbc-ringed-projection-mate-exact` is replaced by the
existing abstract projection-map mate equation. The geometric ringed-topos datum
remains in the statement interface through `def-weil-pbc-ringed-topos-morphism`.

The ordinary comparison is determined by its underlying right equation and Hom
mate equation; the fixed underlying inverse-image comparison is determined by its
Hom equation. Generalized pure tensors determine its tensorator, and the monoidal
unit laws determine its unit. Thus the existential ordinary data are normalized
objects, not arbitrary choices from mere existence. The derived tensor data are
likewise fixed by their representative normalizations and localization descent.

The ordinary and tensor source dependencies are retained by the two new nodes.
They are relocated within the argument, not pruned globally. The etale source
route is retained unchanged. No library module is withdrawn and no global module
pruning is claimed. The following top-level `tool_uses` entries are removed:
`lem-sfb-constant-scalar-geometric-adjunctions`, `lem-pc-kflat-resolution`,
`lem-pur-cochain-pullback-tensor-coherence`,
`lem-sfb-ringed-equivalence-resolving-tensor-descent`, and
`lem-weil-pbc-right-derived-plus-injective`. The first four remain dependencies
of the new ordinary or tensor nodes; the last is replaced by fully faithful
adjunction restriction. No new top-level `tool_uses` approval is added.


## Where the brief, the DAG or earlier work was wrong

The ordinary and tensor declarations in the original dependency list are not
literally the specialized interfaces needed by this theorem. In particular, the
ordinary geometric-adjunction lemma uses constant RingCat sheaves, whereas the datum
here uses the forgotten constant CommRingCat sheaf and restriction along its canonical
comparison. The tensor statement must also retain both prescribed representative
normalizations and the square with an arbitrary normalized left comparison. The two
new nodes specify these missing specialized conclusions.

The original K-injective chain calculation and the separate bounded-below
representative calculation can be replaced by the existing derived exact-mate theorem
and the fully faithful restriction of the derived adjunction. This keeps the same
canonical units and counits and avoids choosing new resolutions. Generic localization predicates keep the ordinary functors abstract while checking
the normalization proofs. The original concrete equations mixed sheaf zero-morphism
instances and the equal abelian-induced instances, making kernel conversion repeatedly
expand module operations. The definition repair shares the generic equations between
the proofs and concrete predicates; its meaning is checked against the original formulas.

## New nodes

`lem-sfb-constant-module-ordinary-realization` records the ordinary scalar comparison
and generalized-pure-tensor-normalized fixed inverse image (source: Stacks 00YV (6),
03EL and 07A4). Its edge cases include the zero ring, empty sites, independent
universes, and sites without points; the proof uses generalized sections throughout.

`lem-sfb-constant-module-tensor-square-descent` records the ordinary ringed monoidal
structure, the two normalized derived monoidal structures, and their scalar square
(source: Stacks 07A4, 0FPQ and 0FPT). Its representative hypotheses are K-flatness,
without a boundedness assumption. The scalar comparisons are already normalized,
so arbitrary monoidal choices are not admitted. Its zero-ring and identity-morphism
cases reduce to the same universal pairings and localization equations.

The definition repair and consumer checks are recorded in
`coord/changes/A6-constant-module-localization-conditions.md`.

The first delivery attempt pushed nothing: compilation against the previously built
bounded-below consumer timed out. Rebuilding that consumer with the shared abelian
instance selection is part of the repair packet.

The final proof removes the experimental monoidal instance priority and restores the
recorded scalar instances before the unchanged etale data interface. There is no
increased time or heartbeat limit in the delivery. The expanded-equation regression
attempt timed out and is not claimed as a passing check; the formulas are preserved
by the explicit generic specialization shown in the change record.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
