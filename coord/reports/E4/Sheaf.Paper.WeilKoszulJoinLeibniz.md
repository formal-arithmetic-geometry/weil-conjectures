## What changed

Proved the positive-degree zero-extension cases of `koszulJoinSummand_leibniz`.
Split the nonpositive-degree algebraic contraction calculation into the named theorem
`koszulJoinSummand_leibniz_nonpositive` in the same module, with a matching DAG node.

## Proved and sorry left

The original `koszulJoinSummand_leibniz` is proved from the nonpositive-degree theorem
and the vanishing of extension components outside nonpositive degrees. One sorry remains
in `koszulJoinSummand_leibniz_nonpositive`; its node is
`lem-weil-pbc-koszul-join-summand-leibniz-nonpositive`.

## No longer needed

The temporary local exterior-algebra helper lemmas and the direct `KoszulDifferential`
proof route were removed after the nonpositive calculation was split off. No imports
beyond `Sheaf.Paper.WeilKoszulJoinGraded` are needed by the final file.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the substantial transport calculation through the three
extension isomorphisms. This delivery records that calculation as a strictly simpler
nonpositive-degree theorem, leaving only the elementary zero-extension cases in the
parent theorem.

## New nodes

`lem-weil-pbc-koszul-join-summand-leibniz-nonpositive` records the nonpositive-degree
intermediate theorem and its remaining proof obligation.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
