## What changed

The unchanged theorem `CategoryTheory.filteredDerivedOperationLifts` is now assembled
from three strictly partial construction results. Its exact-termwise clause is proved by
`CategoryTheory.exactFilteredLocalization`: the additive filtered object action induces
an additive homotopy functor, preserves graded quasi-isomorphisms by conjugating through
the evaluation comparisons and the ordinary exact derived functor, and descends through
localization. The proof constructs shift compatibility, proves triangulatedness by
precomposition, and descends total/graded comparison isomorphisms explicitly. The final
record retains the given step-inclusion and localization equations.

To state the construction subproblems without an import cycle, the original 29 records,
definitions, inductives and their instances/attributes moved unchanged into
`Sheaf.CategoryTheory.FilteredDerivedOperationStructures`. The original module publicly
imports it and retains all original public imports. A byte comparison confirms that the
entire moved declaration block is unchanged, apart from trailing whitespace at the end.
The original theorem's statement is unchanged. No file under `lean/WeilConjectures` changes.

Six Lean modules compile together in sandbox import order, without warnings. The latest
successful lcompile result is `020c07c2af5faf5c4b59390c`: structures 1.7 s, generic adjunction
1.7 s, object action 1.8 s, geometric specialization 2.0 s, localization descent 6.3 s,
and final assembly 5.2 s. These are cached-queue single-file compilation measurements;
the first full compile of the structures module was 33.2 s, also below 60 s.
The direct-importer scan and `tools/downstream.py` find zero external Lean importers of
the item. Therefore there are no consumer adaptations to compile. The unit
`sk-i-global-additivity`, its current blueprint text, and the parent trace-additivity
node remain intact. This is a decomposition inside the existing seven-step node route.

Change record: `coord/changes/C8-filtered-operation-structure-relocation.md`.

## Proved and sorry left

One of one original textual holes closed: `CategoryTheory.filteredDerivedOperationLifts`
(node `lem-trf-filtered-derived-operation-lifts`). This is a decomposition, not a
sorry-free proof: three lower holes were added, so the delivery's textual net is -2.
The upper theorem has a complete Lean proof from these construction results, and
`CategoryTheory.exactFilteredLocalization` has a complete localization-descent proof
from the object-action subproblem. No `sorry` remains in the item module, structures
module, or localization module.

Every remaining/new hole, each the whole proof of a public named theorem in its own module:

- `CategoryTheory.exactFilteredObjectAction`, node
  `lem-trf-exact-filtered-object-action`, module `Sheaf.CategoryTheory.FilteredExactObjectAction`.
  This concerns filtered objects only: additive action, total/graded comparison and step
  inclusion. It has no derived localization or adjunction conclusion.
- `CategoryTheory.filteredDerivedAdjunctionConstruction`, node
  `lem-trf-filtered-derived-adjunction-construction`, module
  `Sheaf.CategoryTheory.FilteredDerivedAdjunctionConstruction`.
  This is original Steps 2–3: a common right-derived lift and its exact-left-adjoint
  adjunctions. It excludes arbitrary exact-functor existence and all geometry.
- `AlgebraicGeometry.ProEtale.proEtaleFilteredOperationPackage_exists`, node
  `lem-trf-proetale-filtered-canonical-construction`, module
  `Sheaf.CategoryTheory.ProEtaleFilteredCanonicalConstruction`.
  This is the geometric specialization, original Steps 4–7, including the actual
  comparison maps, compactification formulas, clopen refinements and pasting equations.
  It has no assertion for arbitrary abelian categories.

Each hole has the source, a complete argument in its declaration docstring and a matching
DAG node. No arbitrary witness is used to define new public data, and there is no hollow
definition or new axiom. The existing structures remain real explicit constructions.

## No longer needed

No mathematical module is withdrawn, and no mathematical prerequisite is claimed pruned.
The 22 original proof dependencies remain needed by the new partial construction nodes
or the unchanged structures. The parent proof now directly uses only the proved exact
localization lemma, the generic filtered-adjunction lemma and the geometric specialization.

The following original private proof imports are removed from the item, because the final
assembly does not use their declarations directly. Their mathematical work is retained in
the DAG of the appropriate construction subproblem:

- `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.CategoryTheory.FilteredFunctorGradedComparison`
- `Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`

The parent's old top-level `tool_uses` approvals are removed because those direct edges
are now delegated to the new construction nodes. Precisely these entries are removed:
`lem-weil-pbc-localization-universal-property`, `lem-weil-pbc-dplus-injective-representative`,
`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-grothendieck-functorial-injective-embedding`,
`prop-weil-pbc-proetale-constant-exact`, `lem-cbc-proetale-extension-zero`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-cbc-proetale-extension-zero-base-change`, `lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-cbc-compactifiable-compatible-tower`, `lem-cbc-strict-tower-proper-open-calculus`.
Their previous explanations in `split_report` stay untouched as historical review material.

## Where the brief, the DAG or earlier work was wrong

No false statement or route error was found. The stated dependencies do not directly
provide the additive action on finite filtered objects, its right-derived comparison
construction, or the geometric package. The delivery makes these genuine missing
constructions explicit, and proves the intervening localization descent in Lean.
The model equivalence and graded-comparison lemmas are usable prerequisites, rather than
replacements for these constructions. In particular ordinary graded comparison does
not assert that an arbitrary ordinary transformation has a filtered lift.

Edge cases checked in the new statements and written arguments: zero filtered objects,
zero functors, degenerate prescribed intervals (only zero objects), unrestricted finite
filtrations, a nonexact left exact functor (graded commutation is used only on split
filtered injectives), identity scheme maps, and the zero coefficient ring. All retain
the required hypotheses. No general graded-commutation claim for left exact functors
on arbitrary filtered objects has been added.

## New nodes

`def-trf-filtered-operation-lift-structures` attaches all 29 unchanged existing declarations
to the new structures module. Its full statement lists the operation, adjunction,
canonical-map and coherence data; it asserts no existence.

`lem-trf-exact-filtered-object-action` isolates the object-level construction from Step 1.
It is strictly smaller than the termwise derived lift and records the necessary natural
graded comparisons needed for the descent proof.

`lem-trf-exact-filtered-localization` records the completed Lean proof descending that
object action. It uses the localization universal property and ordinary exact derived
functor; it introduces no hole.

`lem-trf-filtered-derived-adjunction-construction` is the original filtered-injective
construction and Hom-adjunction calculation of Steps 2–3, with one common right-derived
lift for all exact left adjoints.

`lem-trf-proetale-filtered-canonical-construction` is the original geometric construction
of Steps 4–7. It retains the actual canonical mate maps and clopen projection calculation,
including both ordinary and filtered pasting; no arbitrary transformation replaces them.

The source for the first three is Stacks derived.tex, filtered derived categories and
Tags 015Q–015V/05U2/05TY. The geometric construction additionally follows the original
Varshavsky §§5.2.1–5.2.2 argument and the parent's cited geometric nodes. Actual LeanSearch,
LeanFinder, Loogle and Mathlib grep searches were run through msearch, plus direct rg of
both library roots. Hits supply ordinary derived and localization APIs, not the missing
filtered constructions. Blueprint searches for `filtered derived operation` and
`filtered injective` returned no duplicate blueprint node. The existing parent node is
the source of these strictly partial steps; no duplicate theorem was introduced.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
