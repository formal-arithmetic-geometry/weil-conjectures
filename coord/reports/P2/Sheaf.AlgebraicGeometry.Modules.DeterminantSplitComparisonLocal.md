## What changed

Retained the upstream repair of `determinant_split_comparison_restriction`: the theorem now
expresses naturality through an explicit natural linear family (`dNatural`), pointwise equality
`hd`, and the naturality equation `hn`. This rules out the reviewed rescaling counterexample.
The family name was made explicit in the declaration and DAG statement while preserving the
interface expected by the existing caller.

## Proved and sorry left

`determinant_split_comparison_local` and `determinant_split_comparison_restriction` contain no
`sorry`. Both are already proved in the repository baseline: holes closed in this delivery: none;
holes added: none; holes left in the delivered modules: none. This is an interface-record repair,
not new proof progress.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The upstream review correctly rejected the older unconstrained `c` statement. The repository’s
already-landed repair replaced that generator-only hypothesis by the natural family `dNatural`
with `hn` and `hd`; this delivery records that corrected interface without breaking the caller.

## Forced adaptations

None in this delivery. The packet diff contains only the natural-family binder rename; the earlier rank-argument removal belongs to the previous repair.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version and checked the unchanged caller. The local construction proof
   and the caller preserve all existing declaration signatures; the restriction theorem's binder
   rename is recorded in the existing change record, and the DAG statement now matches the Lean
   declaration exactly. Verdict: pass.
2. Compiled the delivered module and the unchanged caller against it with `lcompile.py`; there are no errors, warnings, `sorry`, or
   forbidden declarations. The restriction proof is direct substitution into `hn`, and the local
   proof uses the two stated linear-map lemmas. Verdict: pass.
3. Checked the restriction statement on the zero-rank and empty-open edge cases: it is a pure
   naturality transport statement and imposes no extra hypotheses. The natural linear family and
   pointwise equality are exactly the assumptions needed; no new statement was added. Verdict:
   pass.
4. Checked the proof route and imports against the DAG. Both linear-map dependencies remain in
   the local route, the caller retains the restriction step, and no imports or proof dependencies
   became unnecessary. Verdict: pass.
5. Checked the DAG node, proof text, proof dependencies, and unit route against the repaired Lean
   source. The node's `statement` and `lean.statement` are byte-for-byte the declaration statement;
   the existing change record documents the binder rename. Verdict: pass.

Changed the restriction theorem binder from `d₀` to `dNatural`, synchronized the DAG node, and recorded this second reading. No proof body or theorem result changed.

Change record: `coord/changes/determinant-split-restriction-right-inverse.md`.

## Earlier second reading (a previous round; superseded)

1. Compared both sandbox modules byte for byte with the repository. The caller and both
   proof bodies are unchanged. The sole signature edit is the documented `d₀` to `dNatural`
   binder rename in `determinant_split_comparison_restriction`; its elaborated proposition,
   hypotheses, visibility and conclusion are unchanged. The change record contains the exact
   old/new signatures, and the node preserves the previous statement-change history. Pass.
2. Independently compiled both modules in import order using `lcompile.py --all`: no errors
   or warnings. Scanned both sources: no `sorry`, prohibited declarations or hollow definitions.
   Printed axioms for both item declarations from a scratch copy: only `propext`,
   `Classical.choice`, `Quot.sound`. The local proof obtains the uniquely characterized linear
   family, applies local bijectivity, and converts it with `LinearEquiv.ofBijective`; it chooses
   no data from an unproved arbitrary existence theorem. The restriction proof substitutes `hd`
   into `hn`. Pass.
3. No statements or holes were split off. Checked the restriction equation for rank zero,
   empty opens, identity restriction and zero section: substitution proves the same equation
   in every case, without any rank or nonempty hypothesis. The local construction uses the
   given rank equality and retains all assumptions. Searched the library with the alternative
   concepts `existsUnique_topDirectSum` and the comparison declaration names: no omitted direct
   replacement for the sheaf construction was found. Pass.
4. Both proof dependencies of `new-determinant-split-local` are used explicitly; the restriction
   node has no proof dependencies and uses only its hypotheses. The two proof imports are plain
   `import`; public imports supply exterior/tensor sections, locally free rank, short complexes,
   and biproducts in the signatures. No old proof dependency became unused. The unit record
   `sk-thm-picard-rr` and its `realized` fields are untouched; the determinant construction route
   is retained. Pass.
5. Compared each node with the declarations and proof bodies. The local node is unchanged;
   the restriction node's statement and Lean statement match the renamed signature, and its
   elementary proof describes precisely the substitution in Lean. Its empty `proof_deps` is
   correct. No new nodes require additional fields. Pass.

Changes made during this second reading: corrected the progress accounting above to distinguish
already-proved declarations from newly closed holes; refreshed the axiom scratch copy to check
exactly the delivered binder spelling; appended this independent review. No Lean proof,
statement, import, definition, or DAG edit was needed.

## Earlier second reading (a previous round; superseded)

Read the delivered Lean source, both associated nodes, and the corrected change record against
this packet's repository baseline. Only one Lean module is delivered:
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal`. Its only Lean diff is the
natural-family binder rename from `d₀` to `dNatural`; both theorem proofs are unchanged.
The renamed restriction signature matches both `statement` and `lean.statement` in its node.
The local theorem signature also matches its node. No caller adaptation is included:
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison` is identical to the baseline.

Compiled the delivered module with `lcompile.py`: exit code 0, without errors or warnings.
Neither declaration contains `sorry`; no holes are closed or added in this repair. The local
proof still uses the two recorded linear-map dependencies and `LinearEquiv.ofBijective`.
The restriction proof still substitutes `hd` into `hn`, including for rank zero, empty opens,
identity restrictions, and zero sections. Its empty proof-dependency list is correct.
No imports, proof routes, or unit realizations change. The change record and current
`statement_change` now describe only the binder rename and correctly place the rank-argument
removal in the preceding repair. Verdict: pass.

## Second reading by P2

1. Compared every sandbox Lean module with the repository baseline. The caller is identical;
   the entire item diff is the binder rename `d₀` to `dNatural`. All proof bodies, imports,
   definitions, hypotheses and conclusions are unchanged. Checked the change record's exact
   old/new signatures against both files and both node statement fields against Lean. Pass.
2. Independently compiled both modules in import order with `lcompile.py --all`, without
   errors or warnings. A scratch copy printed axioms for
   `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local` and
   `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`: each uses only
   `propext`, `Classical.choice`, and `Quot.sound`. Neither delivered module contains `sorry`,
   forbidden declarations, or hollow definitions. The chosen linear family is characterized
   by an `ExistsUnique` theorem, and both imported construction theorems are proved. Pass.
3. No new statements or split-off holes exist. Read both dependency statements: the local
   proof obtains the unique linear family, then local bijectivity, then uses
   `LinearEquiv.ofBijective`, whose forward map gives precisely the original wedge equation.
   The restriction proof is substitution, valid also for zero ranks, empty opens, identity
   restrictions and zero sections, without added assumptions. Pass.
4. The route uses both recorded local proof dependencies explicitly; restriction naturality
   uses only `hd` and `hn`, with no dependency to prune. The proof-only imports are plain
   `import`; public imports support the signatures. Library searches for `topDirectSum`,
   `split_comparison_local`, and the restriction declaration confirmed the existing direct
   algebraic construction and positional caller. No shorter sheaf construction was found.
   No old dependency is unused. The unit `sk-thm-picard-rr` and its existing `realized` fields
   are untouched, and this delivery bypasses no unit step. Pass.
5. Read both DAG nodes and checked their proof steps, dependencies and origins against the
   actual code. The local node is identical to baseline. The restriction node updates only
   the natural-family spelling and records the statement-change history; its empty
   `proof_deps` matches substitution in Lean. No new nodes require checking. Pass.

Changed during this reading: appended this independent review and refreshed the temporary
axiom check, then removed the scratch source. No Lean, DAG or change-record repair was needed.
Both item declarations were already proved in the baseline: newly closed holes zero, newly
added holes zero, split-off statements zero, pruned modules none.
