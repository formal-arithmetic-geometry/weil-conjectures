## What changed
The existing theorem `AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons`
retains its signature byte for byte. Its proof pairs two new component theorems, separating
its independent unit and left/right comparison obligations. The component statements have
exactly the corresponding conjuncts. Existing public imports supply their signatures;
existing private imports retain the planned geometric dependencies of the deferred components.
The second reading repaired the new docstrings and the DAG records.

## Proved and sorry left
Decomposition only: closed the body hole of
`AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons` by conjunction introduction.
Added two holes:
- `AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons_first`, node
  `lem-pc-supported-open-pushforward-local-comparisons-first`;
- `AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons_second`, node
  `lem-pc-supported-open-pushforward-local-comparisons-second`.

One of one original body holes is replaced; two strictly smaller obligations remain.
Net holes closed minus added is -1. No component has been proved, and the parent still
has `sorryAx` transitively. Scratch `#print axioms` on all three declarations showed exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. There is no definition or data
construction in the delivery.

## No longer needed
None in the import closure. The parent node now directly depends on its two components;
its old dependencies `lem-pc-restrict-derived-direct-image-open` and
`lem-sc-derived-open-restriction-adjunction-exact` remain needed by the component arguments,
so neither node nor module is pruned. The original proof-dependency imports remain private.

## Where the brief, the DAG or earlier work was wrong
The first worker's new component node files copied the full parent natural-language and
Lean statements, copied old review attestations, and were outside `dag/nodes/`, so the
delivery tool would not include them. The parent DAG proof did not reflect conjunction
introduction. The component comments were not proof docstrings and triggered style warnings.
These faults are repaired. The original report called the parent proved without making
explicit that this increases the number of deferred obligations; it is a decomposition.

## New nodes
`lem-pc-supported-open-pushforward-local-comparisons-first` isolates only the adjunction-unit
comparison, with its exact Lean statement, support/zero argument, source, and search record.

`lem-pc-supported-open-pushforward-local-comparisons-second` isolates only the left/right
comparison, with its exact Lean statement, extension-by-zero/adjunct argument, source,
and search record. Both nodes are under `dag/nodes/sec-picard-framework/`.
No interface change or change record is needed.

## Second reading by N1
1. Compared the full Lean diff and programmatically compared the existing theorem signature:
   byte-for-byte identical. No definition, existing signature, visibility or import changed.
2. Compiled the repaired module with lcompile.py: no errors or warnings. Audited all three
   declarations with scratch `#print axioms`: only the three allowed axioms and `sorryAx`.
   The only local sorries are the two reported named component theorems, exactly `by sorry`.
   No axiom, unsafe, opaque, implemented_by, extern, or hollow definition occurs.
3. Read both component statements against Stacks Tag 08DF (1) and (2), and Tag 08BS.
   They are the independent conjuncts, not copies of the parent. Checked T empty, U empty
   (forcing T empty), U = X, and T = X (forcing U = X): zero restrictions and fully faithful
   adjunction identities cover these cases. Arbitrary adjunction structures are handled by
   uniqueness; the adjunct equation gives the necessary inverse on U. Perfectness is an
   unused existing hypothesis, retained unchanged. Supplied complete source/proof docstrings
   and matching nodes. Attempted LeanSearch (service returned Internal Server Error); ran new leanfinder, loogle and grep searches through msearch.py and
   rg in lean/: found underived adjunction ingredients and a support-triangle proof with extra
   quasi-coherence/compactness assumptions, but no reusable theorem proving either component.
   Neither deferred component could be closed by a short application of these ingredients.
4. Read the two original imported dependency modules in full. They provide exact extension
   by zero and the open restriction/direct-image comparison; neither supplies the complete
   supported local calculation. The conjunction split is below the unit level and preserves
   both geometric obligations. Checked sk-thm-picard-duality.json: the parent is not a separate
   realized unit step; no unit route or realized field changes. No dependency is removed from
   the argument's import closure; the two original private dependency imports remain available
   for the deferred source arguments. No shorter complete proof found.
5. Corrected the parent proof/proof_deps/proof_origin to pairing, corrected each component's
   natural-language and verbatim Lean statement, removed copied review attestations, assigned
   correct creation/Lean authorship, and recorded fresh searches. Component proof dependencies
   follow the documented source arguments, including exact extension by zero for the second.

Changes: proper complete component docstrings, restored attachment of the existing parent
proof docstring, fixed formatting, delivered node paths and corrected DAG content, and
honest hole accounting. The mathematical component signatures and pairing proof are retained.
