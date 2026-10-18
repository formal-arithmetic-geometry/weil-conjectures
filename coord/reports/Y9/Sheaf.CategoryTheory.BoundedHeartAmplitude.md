## What changed

Proved `DerivedCategory.bounded_heart_amplitude` in
`Sheaf.CategoryTheory.BoundedHeartAmplitude`, with its signature unchanged.
The proof chooses a representing complex using the existing localization API,
transports the cohomology hypotheses along the comparison isomorphisms, and
inducts on the finite tower of canonical upper truncations. The heart bound is
transported to each single-cohomology term using the functor's shift comparison
and the cohomology shift isomorphism in degree `i - q`. Exactness at the middle
term of the mapped distinguished triangle closes the induction step. Finally
the upper truncation at `b` is quasi-isomorphic to the representing complex.

Added the proof-only import `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
Updated the node's proof, dependencies, proof origin, and obsolete tool approval
to record the APIs actually used. No new definitions or statement changes.

The route follows Stacks derived.tex, Tag 08J5,
`remark-truncation-distinguished-triangle`, and more-etale.tex, Tag 0G2A,
`lemma-derived-lower-shriek-bounded`, proof of (3), both read locally.
The existing upper-bound proof in
`WeilConjectures.CategoryTheory.DerivedCategory.HomologyAmplitude` provided the
shift-comparison and exact-sequence proof pattern; its theorem itself does not
suffice because it bounds all heart objects and only one endpoint.

## Proved and sorry left

Closed the sole original hole: `DerivedCategory.bounded_heart_amplitude`
(node `lem-pur-bounded-heart-amplitude`). Holes closed: 1. Holes added: 0.
Sorries remaining in the delivered module: 0. No split-offs.

The initial complete proof compiled in 2.8 seconds. Subsequent checks remove
its tactic-style warnings and verify the final delivery through the prescribed
compiler and dry-run gates. The finite induction includes `a = b`, negative
indices, and zero objects without separate assumptions. All six universe
parameters and every original hypothesis remain unchanged.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.TruncationDescends` and the
direct dependency and obsolete tool approval for
`lem-weil-pbc-truncation-descends`. Its separate descent/naturality interface is
not used: Mathlib supplies the cohomology comparisons and the terminal
quasi-isomorphism, while the existing `truncation_triangle` theorem supplies the
bounded-below truncation property for the zero base. This is a direct-edge
pruning only; other users of that module may still need it.

No other original imports or dependency nodes were removed. In particular,
`lem-weil-pbc-truncation-triangle` and the cohomology-shift and long-exact-sequence
nodes remain used. The unit `sk-prop-sf-cbc` has empty realized statement/step
lists, and the argument keeps its finite truncation route.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing dependency was found. The planned descent lemma
is stronger than the proof needs; existing Mathlib truncation APIs suffice for
its role. The theorem's original signature was preserved.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
