## What changed

Replaced the first worker's restatement `perfect_local_models_descended_transition_aux`
(with its unused `True` hypothesis) by a real reduction. The existing declaration
`AlgebraicGeometry.perfect_local_models_descended_transition` retains its signature
byte for byte and now obtains finite-stage overlap comparison data, then transports
it to every supplied realization using a proved categorical calculation.

The new module `Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram` records actual
functors, natural isomorphisms and their two coherence equations. Its scheme
specialization fixes the restriction functors and the exact canonical comparison
maps; neither structure chooses data from an existence theorem.
`Sheaf.AlgebraicGeometry.TwoOpenComparisonRealization` proves the generic transport
calculation by naturality, coherence, inverse cancellation and functoriality.
`Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram` states only the
remaining finite-stage overlap obligation, without any global object or realization.
Its proof in words constructs the actual pullback comparison functors and maps.

The item imports both new theorem modules with plain `import`, because only its
proof needs them. Its existing public imports and all existing declarations stay
unchanged. Removed all five old plain proof imports from the item. The four descent
and pullback modules remain proof-plan imports of the smaller overlap theorem;
`SchemeDerivedHomRestrictionTransport` is no longer needed by this reduction.
Removed the unused new `DerivedTwoOpenPullbackDiagram` module and the redundant
`perfect_local_models_two_open_data` wrapper.

Scoped `linter.unusedVariables false` to the existing theorem: its unchanged
statement has dependent Pi binders unused in the conclusion, which the completed
proof causes the linter to report. Their names cannot be changed in this proof-only
interface repair. No kernel check or axiom check is disabled.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.perfect_local_models_descended_transition`
(node `lem-pc-perfect-local-models-descended-transition`).

Proved `AlgebraicGeometry.TwoOpenComparisonDiagram.realization` and its private,
fully proved helper `AlgebraicGeometry.comparison_leg`.

Added exactly one hole:
`AlgebraicGeometry.perfect_overlap_transition_comparison`
(node `lem-pc-perfect-overlap-transition-comparison-diagram`), in its own new module.
It has a source and a complete natural-language proof in its docstring. This
obligation descends only the overlap data and does not quantify over realizations.
The item itself has no remaining sorry. This is a decomposition: one original hole
closed, one strictly smaller hole added, net zero. It is not a claim to have proved
the complete descent theorem without unresolved dependencies.

Every delivered module compiled individually through lcompile.py, in import order,
without errors or warnings. Scratch copies with `#print axioms` checked the structures,
the realization theorem, the new overlap theorem and the original theorem. Only
`propext`, `Classical.choice`, `Quot.sound`, and the permitted transitive `sorryAx`
from the remaining overlap theorem/library dependencies occur. The abstract
realization theorem has no `sorryAx`. No new definition contains a hole or selects
an arbitrary witness from an unproved existence assertion.

## No longer needed

Removed these direct imports of the item:

- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms`
- `Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`
- `Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport`
- `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`

Every former direct proof dependency is replaced:

- `def-pc-derived-open-restriction-maps`: still fixes the statement's canonical maps
  and is a statement dependency of the diagram; not a direct proof step of the item.
- `lem-pc-derived-pullback-open-restriction-universes`: used by the overlap obligation.
- `lem-pc-derived-pullback-perfect`: used by the overlap obligation.
- `lem-pc-perfect-descend-morphisms`: used by the overlap obligation.
- `lem-pc-ringed-spaces-derived-pullback-composition`: used by the overlap obligation.
- `lem-sc-scheme-derived-hom-restriction-transport`: bypassed by the proved abstract
  calculation and definitional identification of canonical localized restrictions.

Thus the first four removed imports are retained transitively by the overlap
module; only the Hom transport module is bypassed by the new route. No claim is
made that any module is unreachable from all targets. The unused sandbox-only
DerivedTwoOpenPullbackDiagram and its wrapper are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's auxiliary statement was the entire item with an extra `True`
hypothesis. Applying it was a restatement, not a proof or valid decomposition, and
there was no corresponding auxiliary DAG node. The claimed two-open-data wrapper
was unused by the original proof.

The first version of the proposed overlap interface quantified over an arbitrary
family of coherent diagrams. Its functors HU,HV,HW were not required to be the
actual derived pullbacks, so the proposed natural-language descent proof did not
justify that universal assertion. The repaired interface existentially supplies a
diagram constructed from the actual pullbacks and canonical comparison maps,
together with the descended transition. The realization part is proved separately
for any coherent diagram satisfying that overlap equation.

Independent searches used different wording for both overlap descent and coherent
transport; Mathlib supplies mapIso, naturality and inverse cancellation tools, but
no matching overlap descent theorem. Local searches also found
PerfectLocalModelsEventuallyCompatible and PerfectDescentCompatibleLocalData,
which depend on this item and cannot provide an acyclic shortcut. PerfectDescendMorphisms
supplies the central descent tool, not the exact open-base-change transport wrapper.
The source paragraphs were read at Stacks Tags 09RE and 09RF; compatibility and
composition were checked at Tags 08DW and 0D5S. The local literature checkout is
not populated on this machine; the primary Stacks pages were read directly.

The first dry run exposed the signature parser treating Lean pipe projection
notation as a proof separator. The three new localized restriction expressions
were written with ordinary projection notation instead, with the same Lean type;
the verbatim node signature was refreshed. No checking tool was edited or bypassed.

## New nodes

`def-pc-two-open-comparison-diagram` records both the generic coherent diagram and
its scheme specialization. All data and equations are genuine structure fields,
with no choice of inhabitant. Module: TwoOpenComparisonDiagram.

`lem-pc-two-open-comparison-realization` records the fully proved naturality
calculation for every supplied realization. Module: TwoOpenComparisonRealization.

`lem-pc-perfect-overlap-transition-comparison-diagram` records the single remaining
finite-stage overlap obligation. It isolates the descent portion of the old plan,
constructs canonical comparison data in its proof in words, and has no global
realization conclusion. Module: PerfectOverlapTransitionComparisonDiagram.

There is no statement/definition change to an existing declaration, so no change
record is needed. The original node changes only proof, proof_deps and proof_origin.

## Second reading by G2

1. Compared the item with the repository using diff and raw signature slices.
   The existing signature is byte for byte identical, and its docstring and public
   imports are unchanged. No other existing module is delivered. Verdict: pass.
2. Compiled all four modules through the required runner, and checked scratch
   `#print axioms` output. The sole direct sorry is the named overlap theorem;
   there is no forbidden escape or hollow definition. The generic realization
   proof has only standard axioms. Verdict: pass as a decomposition.
3. Reviewed the overlap obligation against Stacks 09RE/09RF and its full proof in
   words. It contains only local objects and one overlap equation, strictly less
   than the item's realization conclusion. Checked empty, disjoint and equal opens,
   and a singleton or non-strict directed preorder: no strict-growth requirement
   or nonempty-open assumption enters the argument. Reviewed the abstract theorem
   by its explicit categorical proof; it even permits a degenerate overlap category.
   Three search kinds and independent query wording are recorded. Verdict: pass.
4. The proof now proves the realization step and leaves only overlap descent.
   Removed the unused wrapper, redundant module and all unused direct proof imports.
   Read dag/units/sk-thm-picard-semicon.json: its realized arrays are empty, and no
   realized unit statement/step is bypassed. The descent-of-c-before-gluing route
   of the parent blueprint is retained. Verdict: pass; net holes zero.
5. Checked all four node records against declarations, verbatim Lean signatures,
   proof steps and dependency unions. The old node has only permitted proof-field
   edits; each new node has its origin, source, searches, blueprint provenance,
   chapter/unit, created and Lean records. Verdict: pass.

Second reading changed: removed the full-statement auxiliary and `True` marker,
repaired the unjustified arbitrary-diagram quantification, proved realization
transport, split only overlap descent, pruned direct imports, and completed the
DAG and honest decomposition report.
