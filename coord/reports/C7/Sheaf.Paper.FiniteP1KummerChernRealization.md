## What changed

Added two strictly lower proof steps and imported them into
`Sheaf.Paper.FiniteP1KummerChernRealization`. The item theorem now obtains the
finite line comparison isomorphism, specializes `FiniteChernNormalization` to
the pulled-back hyperplane class, and invokes the boundary transport step.
The two lower steps remain named public theorems with documented source and
blueprint tags.

## Proved and sorry left

The original theorem `finiteP1_kummer_chern_realization` is reduced to the two
named lower statements. The delivery adds the following two sorries:

- `finiteP1_kummer_comparison_iso`, node
  `lem-sfb-finite-p1-kummer-comparison-iso`;
- `finiteP1_kummer_chern_realization_of_boundary`, node
  `lem-sfb-finite-p1-kummer-boundary-transport`.

No definition contains a sorry.

## No longer needed

The original direct proof dependencies are replaced by the two split steps.
No imported mathematical module is withdrawn; the remaining definitions are
needed by the two statements and by the parent comparison theorem.

## Where the brief, the DAG or earlier work was wrong

The original three-step plan conflated construction of the comparison
isomorphism with transport of the normalized finite boundary equality. They
are separate obligations: the first is independent of Chern normalization,
and the second assumes the finite boundary equality and a specified line
comparison. The node copy records this split and its reduced proof edges.

## New nodes

`lem-sfb-finite-p1-kummer-comparison-iso` records construction of the
normalized finite line comparison isomorphism.

`lem-sfb-finite-p1-kummer-boundary-transport` records transport of the finite
boundary equality through the scalar and site comparisons. Both node files are
included in this delivery.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
