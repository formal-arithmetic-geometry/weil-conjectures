## What changed

Proved all six supporting theorems in `Sheaf.RingTheory.RetainedLocalization`, with every
existing signature, visibility, definition, and import unchanged. Added the proved private
helper `transition_selector` to calculate selector images at any refining partition stage.
The unit proof uses a common stage supplied by `PrincipalWLocalization.index_isFiltered`,
the cocone equations, and `IsLocalization.Away.isUnit_of_dvd`. Both transition laws use
`IsLocalization.algHom_ext`.

Updated `def-weil-pbc-retained-localization` only in `proof`, `proof_deps`, and
`proof_origin` to record these arguments and the existing principal-w-localization dependency.
No new modules, statements with postponed proofs, or definition changes were needed.

## Proved and sorry left

Closed all six original holes, in namespace `PrincipalWLocalization.Retained`:

- `parts_valid`
- `selector_idempotent`
- `neighborhood_isFiltered`
- `selector_isUnit`
- `transition_id`
- `transition_comp`

The private helper `transition_selector` is also fully proved. No `sorry` remains in the item,
and no holes were added or split off. These are proofs from the existing library: the imported
`Sheaf.RingTheory.PrincipalWLocalization` retains its pre-existing proof obligations, including
`index_isFiltered` and its diagram laws. This delivery does not claim to close those dependencies.
All six declarations belong to `def-weil-pbc-retained-localization`.

Single-file compilation passed without warnings. The general partition proof treats empty E,
E equal to the whole spectrum, and an empty spectrum without a nontrivial-ring hypothesis.
In the refinement calculation, nonemptiness is used only for actual child parts, so empty
partition products require no special assumptions. The localization argument also works when
localizing at zero (the resulting ring is allowed to be the zero ring).

## No longer needed

None. No imports were removed. The sole public import,
`Sheaf.RingTheory.PrincipalWLocalization`, is required by the existing statements and
constructions, and its filtered-index theorem is used by the proof. No existing proof-dependency
nodes or modules have become unnecessary. The explicit construction of a separate common
intersection partition in the selector-unit docstring is unnecessary: any common refinement
from the existing index theorem suffices. No node or module separately encodes that construction.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement errors were found. This definition node had empty `proof` and
`proof_deps` fields even though its Lean module had six named supporting obligations; their
arguments were available in the existing declaration docstrings. The delivery records their
proofs and the principal-w-localization dependency explicitly. The blueprint unit route stays
unchanged.


## Second reading by E1

1. **Interface preservation: pass.** Read the complete repository/sandbox diff and checked
   all thirteen existing declarations with the stage-3 declaration parser. Every existing
   signature, visibility, definition body, attribute, and import is unchanged; only the six
   theorem proofs and the new private proved helper differ. No target or other module is
   changed, and no change record is required.

2. **Proof and trust audit: pass.** Independently compiled the delivered module through
   `lcompile.py`: exit 0, no warnings, 2.2 seconds. A scratch copy prints axioms for all
   thirteen existing declarations and the private `transition_selector`. The only axioms
   reported are `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`.
   `parts_valid`, `selectorIndex`, and `neighborhood_isFiltered` use only the standard
   axioms; selector/colimit-dependent declarations retain the existing principal diagram's
   postponed proofs. Read that dependency's definitions, diagram laws, and
   `index_isFiltered`; no local `sorry`, forbidden declaration, or hollow construction is
   introduced. Choosing a common refinement occurs inside a proof, not in a definition
   selecting arbitrary data from an unproved existence result.

3. **Split statements and small cases: pass, no splits.** No new public statement or
   postponed proof was added. Checked the private helper coordinate by coordinate: a child
   lies in its parent, the parent is E or its complement, and a child in both would contradict
   its required nonemptiness. This proves the exact indicator identity used by the unit
   proof. Empty E, universal E, empty spectrum, empty partition, E = F, and localization at
   zero require no additional hypotheses. The membership/uniqueness proof omits exactly the
   empty parts, and reverse inclusion has the required arrow direction.

4. **Route and pruning: pass.** Rechecked Mathlib by an independent LeanFinder query about
   uniqueness of algebra maps from a single-element localization, a grep for
   `algHom_ext|isUnit_of_dvd|algHom_subsingleton`, and direct source inspection. The existing
   proof already uses the relevant short Mathlib arguments; `algHom_subsingleton` is an
   equivalent formulation of the two-line extensionality proofs. Searched the upstream
   w-localization and the local principal/retained localization modules for selectors and
   partition constructions; no existing selector transport theorem replaces the helper.
   The sole public import is needed in signatures and constructions. The original node had
   no proof dependencies to prune; its principal-localization dependency is genuinely used.
   Read `dag/units/sk-thm-properbasechange.json` including all three `realized.steps`, and the
   corresponding section text in `dag/notes`: these supporting construction proofs replace
   no unit step and preserve the unit route. `## No longer needed` is complete.

5. **DAG agreement: pass.** The node diff changes exactly `proof`, `proof_deps`, and
   `proof_origin`. Its six recorded steps match partition validity, coordinate idempotence,
   filtered neighborhoods, selector transport to a common refinement, the absorbing-product
   identity and localization-unit lemma, and localization-map uniqueness. The union of step
   dependencies is exactly `def-weil-pbc-w-localization`, matching `proof_deps`; its Lean
   record points to the dependency module used in the proof. There are no new nodes to audit.

Second reading changed this report only, adding the independent checks and their trust
limitations. No Lean or DAG repair was needed. Six original holes are closed, zero are added,
and zero are split off; this is not a decomposition claim or a claim that the imported
principal-localization module is already proved.
