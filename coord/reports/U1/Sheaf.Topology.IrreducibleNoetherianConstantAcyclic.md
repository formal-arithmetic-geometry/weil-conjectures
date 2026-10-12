## What changed

Replaced the sole `sorry` in `TopCat.irreducible_noetherian_constant_acyclic`
with the two-step proof already specified by its DAG node. Its signature,
including both universes and the Noetherian hypothesis, is unchanged.

For a restriction to a nonempty open, use `TopCat.irreducible_constant_sections`
and its compatibility equation to lift a section through the additive
identification with the coefficient group. For a restriction to the empty
open, Mathlib's `TopCat.Sheaf.isTerminalOfEqEmpty` identifies the section
object as zero, so restriction is surjective. Convert these surjectivity
proofs to epimorphisms to obtain `TopCat.Sheaf.IsFlasque`.

Apply `TopCat.Sheaf.IsFlasque.subsingleton_H'_top` from
`Sheaf.Topology.FlasqueZariskiAcyclic` (the recorded declaration of
`lem-sc-topological-flasque-acyclic`). This declaration uses Ext universe `u`;
Mathlib's `CategoryTheory.Abelian.Ext.chgUniv` transfers the result to the
original, arbitrary Ext universe `w'`. The added proof import
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt` supplies
`HasExt` at universe `u`; the remaining category instances are already
available through existing imports. The added flasque-acyclicity import
is also non-public. `Sheaf.Topology.IrreducibleConstantSections` is now
a non-public proof import; the redundant direct import of
`Mathlib.Topology.Sheaves.Flasque` is removed (the acyclicity module imports it).

The proof follows the existing node's route exactly, so no node change is
needed. Read the source at https://stacks.math.columbia.edu/tag/02UW: its
proof is precisely the nonempty/empty restriction calculation followed by
flasque acyclicity. The local literature checkout contains only its lists,
so the source was read on the official Stacks site.

Searches through the prescribed `msearch.py` tools: LeanFinder for constant
sheaves on irreducible spaces being flasque found constant-sheaf definitions
but no direct theorem; Loogle found `TopCat.Sheaf.isTerminalOfEmpty`; grep
found no direct Mathlib result. Local searches of both library roots found
the existing section theorem and the recorded flasque-acyclicity theorem.

## Proved and sorry left

Proved `TopCat.irreducible_noetherian_constant_acyclic`
(node `lem-sc-irreducible-noetherian-constant-acyclic`): 1 of 1 original
sorries removed. No `sorry` remains in the delivered module; no new
statements, definitions, or sorries are added.

This is a proof from the existing planned dependencies, not a claim that
all its transitive dependencies are sorry-free. In the current library,
`TopCat.irreducible_constant_sections`
(`lem-sc-irreducible-constant-sections`) and
`TopCat.Sheaf.IsFlasque.subsingleton_H'_top`
(`lem-sc-topological-flasque-acyclic`, also
`lem-sc-zariski-flasque-acyclic`) remain the existing named inputs with
`sorry`. Neither dependency is copied or modified in this delivery.

Validation: the required local single-file compiler succeeds without
warnings. The delivery dry run is the final verification step.

## No longer needed

Removed the redundant direct import `Mathlib.Topology.Sheaves.Flasque`;
its definition remains used through `Sheaf.Topology.FlasqueZariskiAcyclic`.
Removed the first worker's redundant additions
`Mathlib.Algebra.Category.Grp.AB` and
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`.
All three planned dependencies remain used:
`lem-sc-irreducible-constant-sections`, `def-sc-zariski-flasque`, and
`lem-sc-topological-flasque-acyclic`. No node or module is pruned, and no
blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is needed. The recorded acyclicity theorem
fixes the Ext universe to `u`, whereas this item allows `w'`; Mathlib's
change-of-universe equivalence supplies the necessary glue. The Noetherian
hypothesis is unnecessary for the source argument, but is preserved exactly
as required. The DAG's flasque-acyclicity dependency is housed in
`Sheaf.Topology.FlasqueZariskiAcyclic`, rather than a separately named
TopologicalFlasqueAcyclic module; its recorded declaration was used.


## Second reading by U1

1. Compared the only delivered Lean module with the repository using `diff`.
   The existing theorem signature, universes, hypotheses, conclusion, namespace,
   and docstring are byte for byte unchanged. There are no definitions or new
   declarations, and no statement change. The import visibility change is documented in
   `coord/changes/irreducible-noetherian-constant-acyclic-imports.md`. Verdict: pass.
2. Independently compiled the module through `lcompile.py` without errors or
   warnings. Scanned the delivered source: no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`. A scratch copy with `#print axioms` for the item
   and both input lemmas reports only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`; the two existing open dependencies are explicitly listed above.
   The restriction argument handles the empty open separately and correctly;
   for nonempty opens the additive equivalences give preimages, with restriction
   compatibility proving equality. The Ext universe equivalence is injective
   and therefore transfers subsingletonness. Verdict: pass as a reduction to the
   existing named open dependencies, not as a transitively sorry-free target.
3. There are no split-off statements or new nodes. Checked empty opens, identity
   restrictions, zero coefficients, and positive degree (degree zero is excluded).
   No vacuous assumption or hidden change of coefficient group is used.
   Verdict: pass; split-off statement search and docstring requirements are vacuous.
4. Searched both library roots and Mathlib for alternative constant-flasque or
   irreducible-cohomology theorems; no shorter direct result was found. Read the
   existing section and flasque-acyclicity declarations. Independently tested
   import removals with scratch compiles: the direct Flasque import and the AB
   and GrothendieckAxioms.Sheaf additions are redundant, including when removed
   together. Retained the HasExt import for the universe transfer. Corrected
   the proof-only section lemma import to non-public. The unit
   `sk-thm-curveestimate` realizes its statement with `thm-sc-proper-cohomology`
   and has no separate realized steps; this delivery follows the existing
   lower-node route and bypasses no unit. No old proof dependency is unused,
   and `## No longer needed` now records all removed imports. Verdict: pass.
5. Read the item's node, the recorded flasque-acyclicity input, and its unit.
   The Lean proof follows the node's two steps exactly and uses all three old
   `proof_deps`; `proof` and `proof_origin` remain accurate. No node edits or
   new-node metadata are required. Verdict: pass.

Changes by the second reader: removed three redundant imports, made the
section-lemma import non-public, and corrected this report's import inventory.
The proof itself was retained. The first dry run requested an import-interface
change record; added
`coord/changes/irreducible-noetherian-constant-acyclic-imports.md`, with every
transitive importer from `tools/downstream.py`. No downstream module uses the
removed public names, and the sole direct importer imports this module
non-publicly and uses only the unchanged acyclicity theorem. Final dry-run
and delivery checks follow.
