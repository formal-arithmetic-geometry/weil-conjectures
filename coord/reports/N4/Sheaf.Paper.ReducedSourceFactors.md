## What changed

Proved `AlgebraicGeometry.reduced_source_factors_through_closed_subscheme` in
`Sheaf.Paper.ReducedSourceFactors` with its original signature unchanged.
Added two proof-only imports:
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
The first supplies the already proved unique factorization from a range inclusion;
the second supplies the canonical reduction lift and its composite equation.
The forward implication is proved directly on underlying points.
Updated the item's node proof, proof dependencies and proof origin to this library route.
The existing docstring describes the expanded Stacks argument and is preserved.
No definitions, public imports, consumers, or existing theorem signatures changed.

Validation: lcompile.py compiled the item cleanly in 2.6 seconds. A scratch copy with
`#print axioms AlgebraicGeometry.reduced_source_factors_through_closed_subscheme`
compiled cleanly and reported only `propext`, `Classical.choice`, and `Quot.sound`.
Both new imports passed the project import-direction check. No hypotheses of nonemptiness,
affineness, quasi-compactness or reducedness of the target were introduced.
The source read was Stacks schemes.tex, `lemma-map-into-reduction`, Tag 0356,
lines 2268-2289, together with the two source-library proofs cited in the node.
The item is not a realized statement or step of unit `sk-thm-p1`; its unit route stays intact.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.reduced_source_factors_through_closed_subscheme`
(node `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`).
Holes left: zero. Holes added: zero. Split-offs: zero.
The axiom check also excludes transitive `sorryAx` dependencies.

## No longer needed

No original import was removed: the original public Mathlib import is needed by the
unchanged statement. Both added proof imports are used.
The following direct planned proof dependencies are unnecessary because the source library
already proves the factorization criterion and constructs the reduction lift:

- `def-sbc-closed-immersion-ideal-sheaf`;
- `lem-weil-pbc-closed-immersion-image-zero-locus`;
- `lem-weil-pbc-affine-open-section-vanishing-prime`;
- `def-weil-residue-field`;
- `lem-weil-pbc-affine-open-spec-points`;
- `lem-weil-pbc-zero-locus-eq-iff-radical-eq`;
- `lem-weil-pbc-affine-opens-basis`;
- `lem-weil-pbc-closed-immersion-lift-ideal-kills-sections`.

The direct proof edges to `def-pc-scheme`, `def-pc-reduced-scheme`, and
`def-weil-pbc-scheme-reduction` are also removed from `proof_deps`; all three remain
unchanged statement dependencies. No separate Sheaf module for any of the old proof steps
is imported. This is pruning of this proof's DAG route; no claim is made that the listed
nodes are globally unreachable from other parents.

## Where the brief, the DAG or earlier work was wrong

The earlier searches missed the exact reduced-source factorization theorem in the source
library's ClosedImmersion complement and the explicit `liftNilradical` construction in
its Subscheme complement. They are in `WeilConjectures.Mathlib`, rather than Mathlib itself.
No mathematical error or interface repair was needed. LeanFinder and Loogle searches via
msearch found Mathlib's kernel-based lift; local source searches found the exact stronger
source-library API, whose signatures and proofs were read before applying them.
No new nodes or change records are required.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
