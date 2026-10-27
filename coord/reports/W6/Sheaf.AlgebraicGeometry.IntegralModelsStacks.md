## What changed

Replaced the original hole in
AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_models_stacks by an explicit
assembly of the cohomological adic criterion, a heart-level scalar-model comparison,
and complete-object and first-residue comparisons. The categorical restriction proof
constructs the selected functor, proves full faithfulness through the inclusions, and
constructs each preimage using the complete-object equivalence and its counit.

Moved the coefficient maps and predicates verbatim into IntegralModelsStacksData to
let the comparison modules import them without an import cycle. The original module
re-exports that module and keeps its original public imports. The statement and every
original definition are unchanged. Added residueCondition as a named copy of the
residue clause, with proved isomorphism invariance, to fix universe inference before
using it in the comparison signature. The change record is
coord/changes/integral-models-stacks-data.md.

IntegralConstantModelRealization constructs the ordinary functor from actual scalar
restrictions and section reconstruction, proves it is an additive equivalence, and
localizes it termwise. IntegralConstantModelConstructibility proves its comparison
on individual sheaves from integralSectionLocalModels and ordinary completed-model
transport. The proof preserves boundedness by exact faithful transport, compares each
homology sheaf, and applies integral_cohomological_adic_criterion. The realization and heart comparison use the identical pbcIntegralDatum ideal
expression, which is definitionally the original uniformizer ideal. No complex is
replaced by its completion.

## Proved and sorry left

Original holes closed: integral_models_stacks (det-lem-integral-models-stacks).
Original holes left: none.

The retained named holes below are presentation lemmas for parts (1) and (2) of
the blueprint unit, rather than aliases or repackagings of integral_models_stacks.

This is a decomposition, not a net reduction in holes: one original hole is replaced
by two genuinely separate presentation results. The additional holes are:

- AlgebraicGeometry.ProEtale.IntegralModelsStacks.completion_transport
  (lem-sfb-integral-models-completion-transport): restriction equivalence on all complete
  complexes, without boundedness, constructibility or Tor assumptions.
- AlgebraicGeometry.ProEtale.IntegralModelsStacks.residue_transport
  (lem-sfb-integral-models-residue-transport): the first-residue etale-origin comparison;
  its given completeness witness supplies only the completeness conjunct.

The ordinary completedConstantModelTransport is also proved: scalar restriction
commutes with pullback by the normalized coefficient-square adjunction, and with
slice restriction by the sectionwise identity. Its local-model equivalence reflects
isomorphisms through the slice coefficient equivalence. The proof cancels the two
scalar restrictions, identifies the scalar maps by their finite projections, and
retains each cover and finitely presented module while repacking the strata.

Proved additional declarations include IntegralConstantModel.pointEquality,
pointComparison, modulesFunctor_isEquivalence, the additive
instances, and IntegralConstantModel.constructible_iff. The main module also proves
isomorphism invariance of its completeness and Stacks predicates and the categorical selected_equivalence.
All new data definitions are explicit functors or localizations of them; no arbitrary
witness of a bare existence theorem is selected.

Validation: all seven delivery modules compiled together in import order with
`lcompile.py --all`. No compiler errors or non-sorry warnings remained.

## No longer needed

No module is withdrawn or pruned. The unit route through the integral cohomological
criterion and complete-object equivalence is retained. The former direct proof imports
RestrictionLocalCompleteness, CoefficientExtensionFinite, ExtensionIntegersDvr,
ProEtaleTorLocalGlobal, ConstructibleProEtaleComparison, IntegralConstantCompletion,
and ProEtaleFiniteTorComparisonNoetherian move below the extracted presentation lemmas
or are available through their public dependencies. They remain mathematically needed
by those comparisons. IntegralCohomologicalAdicCriterion remains a direct private import of the main
module; the realization imports only its coefficient definitions, avoiding an
unnecessary global instance in the heart comparison.
The original public import surface is retained. The new realization and ordinary model
transport do not import ContinuousCoefficientModuleEncoding: the existing scalar-restriction
equivalence is sufficient.

The direct main-theorem dependency list now names the realization, heart comparison,
cohomological criterion, completeness comparison and residue comparison. Its previous
coefficient, topology and Tor dependencies remain dependencies of those comparisons;
none is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical route is appropriate, but its existing declarations use
different coefficient presentations: internal condensed modules, section-ring modules,
and fixed-scalar sheaves on equivalent small sites. The original DAG did not supply
the complete normalized presentation comparisons needed to compose their Lean
signatures. The new nodes state those missing comparisons separately. The ordinary
heart comparison reuses integralSectionLocalModels rather than duplicating it.

A nested composite of equivalence records made the heart comparison exceed the
single-file compile limit. The realization now exposes the actual composite functor,
with a separate equivalence instance and an object equation for the downstream
proofs. This keeps its reductions to scalar restrictions small. The heart proof uses a separate proved helper for the absolute-value presentation,
then composes directly with the point comparison. Avoiding local aliases in that
proof eliminates an expensive kernel conversion (the direct proof checked in 3.7 s). The residue statement uses the existing adic predicate rather than expanding
its large quantified etale-origin clause. The separately named residue clause and
its isomorphism-invariance proof elaborate beside the original scalar definitions,
avoiding unconstrained universe inference.

## New nodes

`def-sfb-integral-models-stacks-data` owns the relocated, unchanged coefficient maps
and predicates, and the named first-residue clause `residueCondition`.

`def-sfb-integral-constant-model-realization` owns the explicit composite scalar
restriction and section-action functor, its proved equivalence and additive instances,
and its termwise derived localization.

`lem-sfb-integral-constant-model-realization` owns the proved heart comparison from
`integralSectionLocalModels` and the ordinary completed-model transport.

`lem-sfb-integral-completed-constant-model-transport` owns the proved generic ordinary
comparison, retaining the strata, covering sieves and finitely presented scalar modules.

`lem-sfb-integral-models-completion-transport` states the comparison on all complete
complexes, without constructibility or boundedness, with a complete proof in words.

`lem-sfb-integral-models-residue-transport` states the first-residue etale-origin
comparison under a given completeness witness, with a complete proof in words.

Change record: coord/changes/integral-models-stacks-data.md.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
