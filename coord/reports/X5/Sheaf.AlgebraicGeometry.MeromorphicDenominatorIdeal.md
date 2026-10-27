## What changed

Proved `AlgebraicGeometry.Scheme.Modules.meromorphic_denominator_ideal_nowhere_dense`
in `Sheaf.AlgebraicGeometry.MeromorphicDenominatorIdeal`, without changing its statement,
definitions, or public imports. Added proved private helpers and private proof imports of
`Mathlib.CategoryTheory.Limits.Types.Pullbacks`,
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, and
`WeilConjectures.AlgebraicGeometry.Modules.StalkExact`.

The proof follows all three steps of the existing node. Stalkwise regular denominators act
injectively on sections of an invertible module; localization followed by sheafification
therefore embeds that module into its meromorphic module. Local surjectivity of sheafification
and affine local trivializations give a fraction m/b. Regularity of the section gives a regular
coordinate numerator a. Pullback membership is equivalent to b*t = y*m; in trivializing
coordinates this is exactly the requested total-fraction-ring membership condition.

For quasi-coherence, extend both projections of a section over D(f) after multiplying by
powers of f, then kill their discrepancy by another power. The ordinary affine localization
criterion gives a presentation on each chosen affine chart, and these charts cover X.
The projections are monomorphisms by the pullback instances. They are surjective on sections
of every subopen of D(b) and D(a), respectively. Exactness of the stalk functor then kills
the respective cokernel stalks there. The complements of the unions of these dense principal
opens are the required closed nowhere-dense sets. This works without Noetherian or
quasi-compact hypotheses on X.

Validation: the complete module compiled without errors or warnings in 28.3 seconds through
`lcompile.py`. Checked that the public theorem statement and public imports are verbatim
unchanged, that all lines have at most 100 characters, and that each added source-library
import passes the import-direction check. The proof also handles empty schemes and empty
charts without nonemptiness or nontriviality assumptions.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.meromorphic_denominator_ideal_nowhere_dense`
(node `lem-sc-hilbert-denominator-ideal-nowhere-dense`).

Zero `sorry` remain in the delivered module. Zero holes added and zero statements split off.
All 26 private helper theorems are proved. Existing meromorphic-module interface theorems are
used as declared; their proofs are outside this item.

## No longer needed

None. The existing principal-open-density dependency and its private import are used.
No original imports, nodes, or modules are pruned. In particular, the Noetherian
`Sheaf.RingTheory.HilbertAffineDenominatorModule` is unnecessary for this argument and was
not imported; it was not a declared proof dependency of this item.

## Where the brief, the DAG or earlier work was wrong

No statement correction or definition repair was needed. The existing node's three-step
route is retained. For the local-to-global support step, the proof explicitly takes the
complement of the union of all chosen D(b), respectively D(a); density of that union follows
because each affine chart lies in the closure of its chosen principal open. Thus the global
closed sets are constructed without assuming that arbitrary unions of local closed supports
are closed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
