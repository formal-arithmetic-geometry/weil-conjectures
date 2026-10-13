## What changed

Replaced the sorry in `AlgebraicGeometry.perfect_local_models_stage_comparisons`
with a Lean assembly of the Tag 09RF two-open step. The original statement and public
imports stay identical. Added the new module
`Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition` for the unresolved
overlap descent and limit-comparison transport. The new theorem supplies only a
transition on the actual pulled local models and local comparisons for any supplied
realization of that transition. It does not assert that a stage object exists.

The item constructs the inverse-image cover, proves pullback perfectness of both
local models, applies `derived_open_gluing_objects` to construct the global stage
object and its local identifications, and proves this object perfect point by point
using `Scheme.local_perfect_of_openRestriction_iso` in the proved private helper
`perfect_of_two_open_models`. This shares the generic perfectness argument before
instantiating it at a stage scheme. Perfect pullback along each
inclusion gives the two perfectness assertions in the unchanged conclusion.
The gluing transition equation then activates the remaining local comparison clause.
The fully proved private helper `glue_perfect_two_open_models` shares the generic
gluing proof before instantiation at a stage scheme. Neither private helper contains sorry; the
construction and combination of the parts remain real Lean in the assigned module.
This is a strict reduction: existence of a global stage object and its perfectness
are proved here, rather than assumed by the intermediate statement.

Added proof imports for the new transition module and `OpenPerfectModelTransport`.
Both modules locally reuse `openComparisonModuleAbelian` and
`openComparisonOverModuleAbelian`, the existing named Mathlib abelian structures
from `OpenSectionsCohomologyModel`, as local instances. This module was already
in the targets' import closure; it adds no unrelated theory to that closure.
Explicit functor types for the overlap restrictions, their composition comparisons,
canonical category-instance bindings, and typed names for the two existing
overlap Hom restriction maps keep elaborated instance expressions shared. These
are representation and inference fixes: no mathematical definition changes.
The main proof keeps the three initial let-bindings in context (`intro Yj X gj`),
instead of expanding all stage geometry by `dsimp`. A scoped unused-variable style
linter setting preserves the original named forall hypotheses: the proof introduces
them under tactic names, so the signature names trigger that style warning. No
mathematical check or kernel check is disabled.
Updated the original node's proof, proof_deps and proof_origin to describe this assembly.

## Proved and sorry left

Closed: `AlgebraicGeometry.perfect_local_models_stage_comparisons`
(node `lem-pc-perfect-local-models-stage-comparisons`). No sorry remains in the item. The private helpers `perfect_of_two_open_models`
and `glue_perfect_two_open_models` are also proved, with no new hypotheses in the public statement.

Added and still sorry: `AlgebraicGeometry.perfect_local_models_descended_transition`
(node `lem-pc-perfect-local-models-descended-transition`). Its entire proof is
`:= by sorry`; its docstring and node describe descent on the directed tail,
transport through cartesian open identifications, and fully faithful preimages
of the local comparisons. This is one hole closed and one hole added, hence a
decomposition with net zero new holes closed, not a sorry-free proof of the result.
The existing `derived_open_gluing_objects`, `derivedPullback_preserve_perfect`,
and `local_perfect_of_openRestriction_iso` are used without changing them.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`,
`Sheaf.AlgebraicGeometry.PerfectDescendMorphisms`,
`Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport`, and
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`.
Their corresponding nodes are no longer direct proof dependencies of the item:
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-perfect-descend-morphisms`,
`lem-sc-scheme-derived-hom-restriction-transport`, and
`lem-pc-derived-pullback-open-restriction-universes`.
They are still needed by the new unresolved transition theorem and are imported
there as proof dependencies. Therefore these
are relocations of dependencies, not globally pruned theory. No module or node
has been established as pruned from the targets' closure. The public restriction
import remains necessary for the unchanged statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or target was changed. The unit record
`sk-thm-picard-semicon` has empty realized statement/step lists, so this decomposition
bypasses no mandated unit realization. The existing source module
`PerfectLocalModelsEventuallyCompatible` has a related interface but imports
`PerfectLocalModelsStageGluing`, which imports this item; using it would be circular.
`PerfectDescentCompatibleLocalData` depends on that same route and additionally
requires Noetherian rings and descent-on-opens hypotheses absent here.

The local Stacks source checkout is not present on this machine. The actual source
proofs were read at https://stacks.math.columbia.edu/tag/09RF,
https://stacks.math.columbia.edu/tag/09RE, and
https://stacks.math.columbia.edu/tag/08DG. The transition universal property is an
explicit refinement of the prescribed c in Tag 09RF; it is not a claim that gluing
has a unique global realization. Any supplied realization yields the local maps.
The remaining transport/coherence work has not been proved in Lean.

Edge cases checked against the new statement: when the overlap is empty its
transition and compatibility equations are vacuous; empty schemes need no pointwise
perfectness witnesses; equal opens use the comparison transition induced by the two
specified isomorphisms; the non-strict preorder uses only ≤, transitivity and directedness.
The statement never chooses definition data from an unproved existence theorem.

## New nodes

`lem-pc-perfect-local-models-descended-transition` records the prescribed overlap
isomorphism at a later stage and its action on any realization of the pulled local
models. It separates that descent/coherence task from the actual object construction
and local perfectness proved in the item. Its source is Tag 09RF's paragraph before
applying Tag 08DG, with full faithfulness from Tag 09RE. The node includes the exact
Lean signature, four search records (LeanSearch was unavailable), inherited chapter/unit and
blueprint ancestry.
Change record: `coord/changes/PerfectLocalModelsStageComparisons-local-instances.md`.
The preflight conservatively flags the local attribute command; the record documents
its local scope and unchanged public signature. No existing definition is changed.

## Second reading by F1

1. I compared the delivered stage-comparison module against the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof code, local proof attributes, and proof imports changed. The new transition module is separately declared and its node records the exact statement.

2. I compiled both delivered modules with `lcompile.py`; both compile without errors or warnings. The item has no remaining `sorry`; the only remaining `sorry` is the named split theorem `perfect_local_models_descended_transition`, with its docstring and DAG node. No forbidden declarations or hollow definitions were added.

3. The split theorem is a genuine intermediate descent-and-transport statement, strictly narrower than the item because it supplies only an overlap transition and conclusions for any supplied realization. Its edge cases (empty overlap, empty opens, equal opens, and non-strict directed preorders) are covered by the equations in the statement. Searches recorded in `searches.jsonl` and the node found no existing Mathlib or library declaration matching it.

4. The proof follows the unit route through derived pullback perfectness and two-open gluing. The shorter generic perfectness helper is used only below the unit statement. Removed imports are no longer used directly by the item and remain dependencies of the split transition theorem, as recorded above; no target-reachable module was incorrectly claimed pruned.

5. The delivered DAG node proof, proof dependencies, source, and proof origin agree with the Lean proof and the report. The unit `sk-thm-picard-semicon` has no realized statement or step entries, so the decomposition does not bypass a mandated unit realization.

I changed only this report by adding the required second-reading record; no Lean statements or definitions were changed during review.
