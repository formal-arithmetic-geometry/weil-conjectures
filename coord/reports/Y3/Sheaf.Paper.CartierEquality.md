## What changed

Completed the proof of `cartier_equality` in `lean/Sheaf/Paper/CartierEquality.lean`.
The proof constructs the finite transcendence basis and complete-intersection cotangent
model, then applies rank-nullity and the finite-extension transcendence-degree-zero
lemma. The change is proof-only.

## Proved and sorry left

`cartier_equality` is proved with no remaining `sorry`s. No new declarations were added.

## No longer needed

No imports or DAG dependencies were removed; all existing proof dependencies are used.

## Where the brief, the DAG or earlier work was wrong

Nothing substantive was wrong. The stated proof plan is sufficient and compiles.

## Earlier second reading (a previous round; superseded)

A second reading should verify that the complete-intersection equivalences are used in
the stated directions and that the final finite-dimensional equality follows from
`trdeg_eq_zero` without changing the theorem statement.

## Second reading by Y3

1. Compared the delivered module with the repository version. The theorem signature,
   declaration visibility, definitions, and imports are unchanged; the only edit is
   proof syntax around the existing `trdeg_eq_zero` application.
2. Compiled `Sheaf.Paper.CartierEquality` with `lcompile.py`; it succeeds without
   errors or warnings. A scratch `#print axioms cartier_equality` reports only
   `propext`, `Classical.choice`, and `Quot.sound`, and there are no `sorry`s,
   axioms, unsafe declarations, or hollow definitions.
3. No statements were split off and no new nodes are present. The existing target is
   unchanged and the proof dependencies are all used by the complete-intersection,
   cotangent-model, and transcendence-degree steps. A search found no duplicate
   declaration that could replace the target.
4. Read the proof from the target downward: the finite transcendence basis and
   complete-intersection model give the coordinate map; the two equivalences identify
   kernel and cokernel with the required cotangent modules; rank-nullity gives the
   cardinal equality; and finite dimensionality supplies `trdeg_eq_zero` for the
   final equality. The complete-intersection unit route and its realized nodes are
   retained, and no imports or DAG dependencies can be pruned.
5. The DAG node's statement, `proof`, `proof_deps`, and `proof_origin` agree with the
   Lean proof. The finite-extension conclusion is obtained by rewriting the proved
   equality, with no added hypothesis or weakened conclusion.

Changed only the proof's explicit `by exact trdeg_eq_zero` elaboration in
`cartier_equality`; no declarations, imports, nodes, or dependencies were added or
removed.
