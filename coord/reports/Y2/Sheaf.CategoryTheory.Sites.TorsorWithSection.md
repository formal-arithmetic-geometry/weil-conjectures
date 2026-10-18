## What changed

Proved `CategoryTheory.Sheaf.Torsor.WithSection.isIsomorphic_equivalence` in
`lean/Sheaf/CategoryTheory/Sites/TorsorWithSection.lean`, following its existing docstring.
Reflexivity uses `Torsor.Iso.refl`; symmetry uses `Torsor.Iso.symm` and the identity
`CategoryTheory.Iso.hom_inv_id_apply` after evaluating the underlying sheaf isomorphism
at the specified object; transitivity uses `Torsor.Iso.trans` and the two section equalities.
All signatures, definitions, visibility, and imports are unchanged. No route change or
new node is needed: this is the elementary equivalence verification already described
in the declaration's proof docstring.

The final proof compiled cleanly through `lcompile.py`. A separate compile with
`#print axioms` verified that both the equivalence theorem and `WithSection.Classes`
depend only on `propext`, `Classical.choice`, and `Quot.sound`; the diagnostic commands
were removed before delivery.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Sheaf.Torsor.WithSection.isIsomorphic_equivalence`
(node `def-amb-torsor-with-section`).

Zero holes remain in the item. Zero holes added; zero statements split off.

## No longer needed

None. The existing public import `WeilConjectures.CategoryTheory.Sites.Torsor`
is needed by the definitions and supplies the torsor-isomorphism operations used by the proof.
No imports, declared dependencies, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof docstring gives the complete elementary argument. The node
has no additional proof dependencies, and the unit's route is unchanged.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
