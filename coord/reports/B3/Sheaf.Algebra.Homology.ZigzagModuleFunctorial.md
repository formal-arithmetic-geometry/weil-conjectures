## What changed

Removed the top-level private `index_eq_iff` declaration, which duplicated the
word-for-word theorem statement already present in
`Sheaf.Algebra.Homology.ZigzagToRowCokernel`. The proof now introduces the same
`Subtype.ext_iff` fact locally inside the two private generator calculations
that need it. The public theorem and all signatures are unchanged.

## Proved and sorry left

`HomologicalComplex₂.zigzagModule_functorial` remains fully proved. No `sorry`s
were added or left in the item.

## No longer needed

The duplicate top-level `index_eq_iff` declaration is no longer needed. No
imports, proof dependencies, or other modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private declaration whose statement was
already present word for word in the library. The repair keeps the equality
fact local to the proof, avoiding a duplicate library declaration while
retaining the compiled proof route. No mathematical or interface change was
needed.

## New nodes

None.

## Second reading by B3

1. The delivered module was compared with the repository version. The public
   theorem statement and all existing declaration signatures are unchanged;
   verdict: pass.
2. The module and an axiom scratch copy compile cleanly. There are no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and
   the theorem uses only `propext`, `Classical.choice`, and `Quot.sound`;
   verdict: pass.
3. No statements were split off. The private helper declarations are local
   proof steps, and no duplicate public or library theorem was introduced;
   verdict: pass.
4. The proof follows the unit route through boundary and total-map
   preservation, then quotient representatives for uniqueness, composition,
   and identity. The local `index_eq_iff` facts remove the former duplicate;
   verdict: pass.
5. The DAG node's statement, proof steps, dependencies, and proof origin agree
   with the Lean proof. No imports or proof dependencies became unnecessary;
   verdict: pass.

The second reading changed only this report: it records the checks above and
confirms that the duplicate helper was removed without changing the interface.
