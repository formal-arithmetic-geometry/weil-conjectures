## What changed
Added the strict intermediate theorem `etale_section_lifting_radical_and_henselian`, leaving the full item theorem open. The intermediate theorem records only the radical and root-lifting consequences, rather than restating the item's idempotent-lifting conclusion.

## Proved and sorry left
The item theorem `henselianRing_of_etale_section_lifting` remains sorry. Sorry also remains in `etale_section_lifting_radical_and_henselian`, with node `lem-weil-pbc-etale-section-lifting-radical-and-henselian`; `etale_section_lifting_idempotents` remains sorry with node `lem-weil-pbc-etale-section-lifting-idempotents`.

## No longer needed
No imports or existing proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong
The full descent argument could not be completed within this delivery; only its strict radical/root-lifting part is split off.

## New nodes
`lem-weil-pbc-etale-section-lifting-radical-and-henselian` and lem-weil-pbc-etale-section-lifting-idempotents are the copied DAG node files.

## Earlier second reading (a previous round; superseded)
The item statement and intermediate statement were checked against their Lean signatures. The target theorem now only unpacks the intermediate conjunction; the intermediate `sorry` is explicitly tracked by its node.

## Second reading by F1

1. The delivered module was diffed against the repository version. The target signature is unchanged; the new declaration is an additional strict intermediate statement.
2. The module compiles with `lcompile.py`; the only remaining `sorry`s are the two named theorems listed above. No forbidden declarations or hollow definitions were added.
3. The split statement is true by the cited Stacks Tag 09XI implication and is strictly weaker than the item because it omits finite-algebra idempotent lifting. Its node and docstring match the Lean declaration.
4. The proof route keeps the unit's radical/root-lifting route. No shorter completed proof was found; no imports were removed.
5. The DAG node's statement, proof, proof dependencies, and Lean record agree with the delivered file. The change from the earlier restatement split is recorded above.

Changed the intermediate theorem and its node to remove the restatement of the item; updated this report accordingly.

The final theorem is now obtained by combining the two strict split statements: radical/root-lifting and finite-algebra idempotent lifting.

