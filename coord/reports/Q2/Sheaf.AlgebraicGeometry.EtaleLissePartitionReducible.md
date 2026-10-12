## What changed

Repaired the returned module by removing the top-level private `lisse_of_iso`
lemma, which duplicated the word-for-word declaration in
`EtaleGenericLisseStratum`. Its proof is now a local transport argument inside
`lisse_open_comp`, so the reducible partition theorem and all other helper
proofs remain unchanged. The module compiles and the dry run passes.

## Proved and sorry left

`AlgebraicGeometry.Scheme.nonempty_etaleLissePartition_of_reducible` remains
fully proved. Holes closed: `AlgebraicGeometry.Scheme.nonempty_etaleLissePartition_of_reducible`
(the one original hole). Holes added: none. Split-off statements: none.
The axiom check on the current compiled dependencies shows only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

The duplicate top-level `AlgebraicGeometry.Scheme.lisse_of_iso` declaration is
no longer present. No imports were removed relative to the repository version. The old proof
dependency `lem-weil-pbc-noetherian-finite-components` is no longer used and
was removed from `proof_deps`: the proof uses binary closed decomposition
instead of enumerating irreducible components. This dependency is a Mathlib leaf,
`AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian` in
`Mathlib.AlgebraicGeometry.Noetherian`. That module remains publicly imported
because the unchanged signature needs `IsNoetherian`; no module is pruned
by this delivery.
The remaining proof uses the open-pullback, stalk-germ, inverse-image
composition, and partition declarations. Global reachability pruning remains
the maintainer's responsibility.

## Where the brief, the DAG or earlier work was wrong

The prior delivery was rejected because its private helper had exactly the
same statement as the private helper in `EtaleGenericLisseStratum`, which the
pruning checker treats as a duplicate library theorem. Since that declaration
is private and cannot be imported by name, the transport proof is kept local
inside `lisse_open_comp` while preserving the original theorem's behavior and
signature.


## Second reading by Q2

1. PASS: compared the entire module with the repository using `diff`. The
existing theorem signature is byte-for-byte unchanged. No existing definition,
statement, or public import changed, and no change record is required. The
additions are proved private helpers and the replacement of the original sorry.

2. PASS: compiled the delivered module with `lcompile.py` (5.2 seconds, no
errors or warnings). Compiled a fresh scratch copy with `#print axioms` for
the main theorem, `lisse_open_comp`, `subtractClosed`, and `unionDisjoint`.
Every result lists only `propext`, `Classical.choice`, and `Quot.sound`. No
sorry or forbidden declaration occurs in the delivered module. The partition
helpers construct their data explicitly from the supplied partitions; they
do not select arbitrary data from postponed existence proofs.

3. PASS: no statements were split off and no holes were added. Checked the
helper arguments on zero-length partitions, empty differences, and overlapping
closed supports: Fin.append permits zero lengths, subtraction retains empty
strata, and the second support is made disjoint by removing the first.

4. PASS: searched the library and upstream sources for lisse transport, open
pullback, reducible partitions, subtraction, and union. The available lisse
transport helpers are private; the local transport argument is appropriate.
The upstream Noether partition union concerns a different structure and does
not replace this proof. All three private imports are directly used only by
the proof; the two public imports supply types in the unchanged signature.
The binary decomposition is shorter than component enumeration and retains
the reducible induction step and open-subtraction argument. The unit
`sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps` arrays;
no recorded realization or unit route is removed. The finite-components
dependency was missing from the pruning report and is now listed above.

5. PASS: compared the old and delivered node and read each proof step. Its
`proof`, `proof_deps`, and `proof_origin` describe the binary decomposition,
explicit open subtraction, lisse transport, and finite concatenation in Lean.
Only permitted proof fields differ. No new nodes require checking.

Second reading changed the report only: completed the pruning list, recorded
holes closed and added explicitly, and replaced the outdated claim that the
open-pullback dependency remains postponed with the actual axiom-check result.
The existing theorem docstring describes the older component-enumeration
route; the current route is documented accurately in the node and this report.
