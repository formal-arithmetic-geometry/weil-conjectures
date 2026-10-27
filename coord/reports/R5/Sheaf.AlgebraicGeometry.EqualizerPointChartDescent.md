## What changed

Proved `AlgebraicGeometry.equalizer_point_chart_descent` in
`Sheaf.AlgebraicGeometry.EqualizerPointChartDescent`, with its complete original signature.
Added proved private helpers for the graph-pullback equalizer, its monomorphism and lifts,
the quotient universal property, the affine chart isomorphisms, and field stalks.

The proof constructs the normalized charts using `Scheme.Hom.liftQuotient` on arbitrary
test schemes. Their point maps are open immersions, jointly covering and pairwise disjoint;
`isOpenImmersion_sigmaDesc` and surjectivity then prove the canonical coproduct map is an
isomorphism. The chart equations and overlap compatibility follow by cancellation of the
equalizer monomorphism. Finiteness uses the finite product algebra, étaleness uses the
existing finite-separable-field coproduct theorem, and the exact structural stalk map is
identified with a field localization map. Updated the node's proof, proof dependencies,
and proof origin to match this implementation. No definitions or public interfaces changed.

Validation: server single-file compilation; `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The proof covers empty schemes, empty point sets,
empty charts, and arbitrary overlaps without a separatedness hypothesis.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.equalizer_point_chart_descent`
(node `lem-trf-equalizer-point-chart-descent`). Holes closed: 1. Holes added: 0.
No `sorry` remains anywhere in the delivery, and nothing was split off.
All seven private helper theorems are proved.

## No longer needed

Removed the proof-only import `Mathlib.AlgebraicGeometry.Gluing` and the node dependency
`lem-weil-pbc-scheme-morphism-gluing`. The arbitrary-test factorization is already supplied
by `Scheme.Hom.liftQuotient`; the global inverse is supplied by Mathlib's theorem on a
surjective open immersion after proving disjointness and coverage. Thus explicit gluing
of affine-test factorizations or of local inverse maps is unnecessary. The existing
coproduct-family and finite-affine-coproduct-spectrum dependencies remain used. The
finite-separable-field coproduct theorem and its approved tool use remain used.
No project module is withdrawn or claimed globally unreachable. No unit realization is
bypassed. Temporary trial imports of the closed-immersion and isomorphism modules were
also removed: their public APIs are already available from the existing public imports.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The DAG's two explicit gluing passages
are longer than necessary with the current Mathlib API; the replacement arguments are
recorded in the updated node. The hypotheses `hs` and `hcs` are redundant for this proof:
the graph equations, evaluation normalization, and rational point structure equations
suffice. They remain verbatim in the theorem's signature and are acknowledged locally in
the proof. The theorem and all target statements are unchanged.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
