## What changed

The item module now packages the coefficient-comparison data into an arrow-category
isomorphism using `Arrow.isoMk'`. The comparison data itself is a named intermediate theorem
left as `sorry`, with a new DAG node. No imports were added or removed.

## Proved and sorry left

`exists_baseChangeHomologyMap_restrictScalars_arrow_iso` is proved by the real categorical
assembly from `restrictScalars_baseChange_comparison`. The latter is the only `sorry` left and
is recorded by node `lem-sbc-base-change-restrict-scalars-comparison`.

## No longer needed

None. The original import set remains necessary for the statement and arrow-category
packaging.

## Where the brief, the DAG or earlier work was wrong

The original three-step plan omits a Lean declaration for the derived source/target comparison
and its compatibility with the base-change map. That missing substantial comparison is split
out as the intermediate node above; the final arrow construction is elementary once it is given.

## New nodes

`lem-sbc-base-change-restrict-scalars-comparison` in
`dag/nodes/sec-smooth-base-change/lem-sbc-base-change-restrict-scalars-comparison.json`.

## Earlier second reading (a previous round; superseded)

The item statement is unchanged. The intermediate node is strictly the source/target comparison
and its commutativity equation; the item combines it with the standard `Arrow.isoMk'` constructor.
The theorem remains open only at the derived comparison step.

## Second reading by A2

1. **Statements unchanged.** Compared the delivered item module with the repository version;
the existing theorem signature is byte-for-byte unchanged. The new comparison theorem is a
strict intermediate statement and does not alter the target.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; the only remaining `sorry` is
the named comparison theorem, and no forbidden declarations occur. The arrow theorem is proved
by `Arrow.isoMk'` from the comparison data.

3. **Split-off statement.** Checked the comparison theorem against its node and docstring. It
states exactly the source and target isomorphisms plus their commutativity equation, so it is
strictly weaker than the item and is the necessary derived-functor reduction. Searches found no
existing declaration with this statement.

4. **Pruning and route.** The existing imports are all used by the module's statements or proof;
no import or proof dependency can be removed. The arrow-category packaging follows the unit's
route after the comparison step.

5. **DAG agreement.** Updated the item node's proof and `proof_deps` to match the two proof steps,
and added the comparison node with matching Lean declaration, source, proof description, and
`status: split`.

Changed the module only by adding the documented comparison theorem and replacing the target's
placeholder proof with the `Arrow.isoMk'` construction; added the corresponding DAG node and
updated the item node metadata.
