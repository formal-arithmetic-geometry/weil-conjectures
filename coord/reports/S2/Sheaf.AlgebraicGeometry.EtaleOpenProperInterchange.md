## What changed

Proved `AlgebraicGeometry.Etale.nonempty_iso_etale_open_proper_interchange` in
`Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange` by the existing DAG route.
Extract the derived isomorphism family from `properOpenInterchangeCoherence Λ`,
then specialize it to the horizontal open immersions `pullback.fst p i` and `i`
and the vertical proper maps `pullback.snd p i` and `p`.
Mathlib infers openness and properness of the projections by base change;
`pullback.condition` supplies the commutativity equation.

The theorem's statement, visibility, docstring, imports, and node route are unchanged.
No definition or other module required adaptation. The only proof import,
`Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`, is used.
The assigned file compiled cleanly through `lcompile.py` (28.2 seconds).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.nonempty_iso_etale_open_proper_interchange`
(node `lem-weil-pbc-etale-open-proper-interchange`).

Zero holes remain in the assigned module. Zero holes added; zero split-offs.
This is a proof from the declared dependency
`AlgebraicGeometry.Etale.properOpenInterchangeCoherence`
(node `lem-cbc-proper-open-interchange-coherence`), whose existing proof is still
`sorry`; this delivery does not claim to eliminate that dependency's hole.

## No longer needed

None. No imports, nodes, or modules are pruned. The proof uses all three
existing proof dependencies: the proper/open coherence theorem and the
Mathlib open-immersion and properness base-change instances.
All public imports are retained for the existing statement and exported interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical or process error found. The documented proof route specializes
directly and needs no new intermediate statements. In Lean,
`pullback.condition` has implicit morphism arguments, so the proof uses it
without positional arguments. The stronger coherence theorem does not need
quasi-compactness of the open immersion; the assigned signature is preserved.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
