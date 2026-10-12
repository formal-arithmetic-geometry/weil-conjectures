## What changed

Kept the existing target signature unchanged and proved its body by constructing the flat
completion map with `flat_adicCompletion_of_flat_local`, evaluating its levelwise formula,
and applying `RingHom.completion_map_bijective` for the remaining bijectivity argument.
The new named theorem is in `Sheaf.RingTheory.CompletionMapBijective`. Both new imports are
proof-only imports. Removed the unused `FiniteAfterCompletion` and `FlatModuleCompletion`
imports from the item's module and removed two unused local abbreviations.

## Proved and sorry left

`RingHom.flat_local_completion_iso` has a proof body, conditional on the existing completion
construction and the new bijectivity theorem; it is not axiom-free yet.
`RingHom.completion_map_bijective` is the sole new named `sorry`, in
`Sheaf.RingTheory.CompletionMapBijective`, node
`lem-weil-pbc-flat-local-completion-iso-bijective`. Its docstring supplies the full proof.

## No longer needed

Removed proof imports `Sheaf.RingTheory.FiniteAfterCompletion` and
`Sheaf.RingTheory.FlatModuleCompletion` from the item's module.
The old direct proof dependencies are all replaced:
`def-weil-pbc-noetherian-ring`, `lem-weil-pbc-local-completion-local-ring`,
`def-weil-pbc-adic-completion`, `lem-weil-pbc-finite-after-completion`,
`def-weil-pbc-flat-ring-map`, `lem-weil-pbc-flat-module-completion-flat`,
`lem-weil-pbc-finite-flat-local-free`, `lem-weil-pbc-adic-completion-mod-ideal`.
The local-completion, finite-after-completion, finite-flat-local-free and mod-ideal nodes
remain indirect dependencies of the split bijectivity theorem; they are not globally pruned.
Flat-module-completion remains used indirectly through the broader completion development.

## Where the brief, the DAG or earlier work was wrong

The existing completion-flatness theorem already supplies the map and levelwise compatibility,
so that construction need not be repeated. The earlier split node incorrectly depended on the
item itself, creating a cycle. It also lacked a complete docstring argument and had not been
placed in its own module. The earlier report claimed imports were unused while retaining them.
The second reading repaired these faults. No source statement or existing Lean signature changed.

## New nodes

`lem-weil-pbc-flat-local-completion-iso-bijective` proves bijectivity of an already supplied flat
compatible completion map. It is a strict subargument: the item's existential construction and
levelwise formula are handled separately by the existing `FlatCompletion` theorem. The new node
uses local completion structure, finiteness after completion, and finite flat local freeness;
it has no dependency back to the item. No change records are needed.

## Second reading by F2

1. Compared every delivered module with the repository version. The existing target signature
   is byte-for-byte unchanged. The other module is new; there are no changed definitions.
   Verdict: pass after moving the new statement into its own module.
2. Compiled both modules locally in import order. The only textual sorry is the named
   `RingHom.completion_map_bijective`; no hollow definitions or forbidden declarations occur.
   Axiom probes show the usual permitted axioms and `sorryAx`, as expected for the open
   split theorem and imported open completion construction. Verdict: valid conditional proof.
3. Checked the new statement mathematically: compatibility sends extended maximal ideals into
   each other, so the map is continuous and equals the canonical map by density and separation.
   Finiteness after completion and assumed flatness give a finite free module. The residue-field
   bijection forces rank one and makes 1 a basis. For fields this reduces to the residue-field
   map itself; identity maps and Artinian local rings likewise pass the edge-case check.
   Searches via leanfinder, loogle, grep and rg found no exact duplicate. The finite-flat
   linear-combination lemma in Mathlib handles only the last algebraic step, not the completion
   finiteness and comparison. Verdict: true, strict subargument, not closed in a few minutes.
4. The existing map-construction theorem is the shorter route. Only the two used proof imports
   remain. Inspected `dag/units/sk-thm-p1.json`: this item is not a realized unit statement or
   step, and none of the unit's realized route is bypassed. All replaced old direct dependencies
   are listed above, with indirect uses distinguished. Verdict: pass.
5. Updated the item's proof and proof_deps to the two calls in its Lean body. Removed the
   split node's circular dependency; supplied actual prerequisite nodes, fresh searches and a
   verbatim Lean signature, and updated its module/file record. Verdict: pass after repair.

Second reading changed: unused imports and local abbreviations removed; split theorem moved to
its own module; full natural-language proof added; cyclic and stale DAG metadata repaired;
report corrected to distinguish a conditional proof from an axiom-free theorem.
