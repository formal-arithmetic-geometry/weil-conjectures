## What changed

Proved `CategoryTheory.site_covering_isomorphic_family` in
`lean/Sheaf/Paper/SiteCoveringIsomorphicFamily.lean`, with its signature unchanged.
For each index, `IsPullback.of_vert_isIso` turns the compatibility equation into
an actual pullback square. `Precoverage.mem_coverings_of_isPullback` then proves
that the given family is covering. The identity equivalence supplies the
existential reindexing clause. Updated the node's proof and proof_origin to
record this direct route; proof_deps remains the site-definition node.
No imports, definitions or theorem statements changed.

## Proved and sorry left

Closed the sole hole: `CategoryTheory.site_covering_isomorphic_family`
(node `lem-weil-pbc-site-covering-isomorphic-family`). No sorry remains in the
item, and no hole or new declaration was added. This is a full proof, not a
decomposition; it uses only Mathlib results and no sorried dependencies.
Local single-file compilation passed without warnings. The delivery dry run
checks server compilation and the declaration's axioms as well.

## No longer needed

No imports removed, and no named dependency node or module is pruned.
The existing public import `Mathlib.CategoryTheory.Sites.Precoverage` is needed
by the signature and supplies both lemmas used by the proof.
The old plan's chosen pullbacks, comparison isomorphisms, singleton-cover
composition, and sigma-type reindexing are unnecessary for this Lean statement.
The `HasIsos`, `IsStableUnderComposition`, and `HasPullbacks` hypotheses remain
unchanged but are not used by the proof. The site-definition dependency stays.
No node realizing a unit statement or proof step is bypassed: this item is not
in `sk-thm-p1.realized`.

## Where the brief, the DAG or earlier work was wrong

The node's earlier Mathlib search correctly distinguished indexed Stacks
families from presieve coverings, but that distinction does not obstruct the
current Lean signature. Its `IsStableUnderBaseChange` hypothesis directly
covers every pullback square, including the given objects and arrows.
Consequently the five-step indexed-family plan can be shortened to the direct
base-change argument above. This does not settle the stronger foundational
question of representing arbitrary Stacks sites; it proves the unchanged
presieve-based statement assigned here.
No open change record names this module or its declaration.
The local literature checkout lacks `literature/stacks-project/sites.tex`;
this proof uses the available Mathlib source and adds no source-dependent holes.

Edge cases: the argument applies to an empty index type without selecting an
index, to repeated arrows, and to arbitrary object and hom universes in the
existing signature. Both covering clauses use the same verified covering fact.

## Second reading by Y3

1. **Unchanged declarations.** Compared the delivered module and node with the repository versions. The theorem signature and all existing declarations are byte-for-byte unchanged; the node changes only `proof` and `proof_origin`.

2. **Proof and axioms.** Compiled the module locally with no errors or warnings. The theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and dependencies.** No statement was split off or added. The proof uses the existing Mathlib lemmas `Precoverage.mem_coverings_of_isPullback` and `IsPullback.of_vert_isIso`; the sole DAG dependency remains `def-weil-pbc-sites-and-cohomology`. The direct route is valid for empty index types, repeated arrows, and arbitrary objects in the stated universes.

4. **Pruning and route.** The proof takes the shorter direct base-change route permitted by Mathlib's stronger `IsStableUnderBaseChange` hypothesis. No import or dependency node is removable, and the unit record's realized route is unaffected because this item is not realized there.

5. **DAG agreement.** The node proof and proof origin describe the compiled proof, and its statement, chapter, unit, and Lean attachment are unchanged. No new node or change record is needed.

Changed only the theorem proof and the corresponding node proof metadata; no imports, signatures, definitions, or statements changed.
