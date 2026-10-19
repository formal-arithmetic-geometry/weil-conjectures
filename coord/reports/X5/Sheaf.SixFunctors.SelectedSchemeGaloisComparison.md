## What changed

Proved `WeilConjectures.TraceFormulaCoefficientConventions.comparisonCoefficientAnnihilator`
without changing its statement. Choose `n = T.coefficients.l ^ T.level`.
The spectral norm extends the p-adic norm, so the coefficient prime lies in the
recorded maximal ideal. The DVR theorem identifies this ideal with the span of the
recorded uniformizer. `Ideal.pow_mem_pow` puts the level-th power of the prime in
the defining quotient ideal. It consequently acts as zero on every coefficient.
The finite base field's cardinality gives characteristic `T.datum.p`, which transports
to its algebraic closure; the distinct coefficient prime and its power are units there.

The three existing comparison/finiteness definitions and their signatures are unchanged.
Updated the proof docstring to state the explicit exponent. Added private proof imports
`Mathlib.Algebra.CharP.CharAndCard` and `Mathlib.RingTheory.Ideal.Operations`.
The server single-file compile passed without diagnostics in 8.0 seconds.

## Proved and sorry left

Closed 1 of 1 local holes:
`WeilConjectures.TraceFormulaCoefficientConventions.comparisonCoefficientAnnihilator`
(blueprint node `prop-trf-scheme-galois-comparison`). Zero holes remain in this module;
zero holes added; zero split off. The imported theorem
`WeilConjectures.FiniteFieldDatum.schemeGaloisComparison` is unchanged and still supplies
the normalized comparison selected by the existing definitions.

## No longer needed

Removed the following redundant direct private imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`
- `Sheaf.AlgebraicGeometry.FrobeniusFactorization`
- `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism`
- `Sheaf.SixFunctors.SchemeFrobenius`
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`

No underlying DAG nodes are declared obsolete: these are dependencies of the generic
comparison theorem, which this module continues to import publicly through
`Sheaf.SixFunctors.SchemeGaloisComparison`. The eight-step comparison route and its
proof dependencies stay intact. The local coefficient-annihilator proof uses the
existing DVR and finite-field interfaces instead of those geometric proof imports.
No module is withdrawn, and no target-reachable geometric result is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned module has one local coefficient-annihilator hole. The node's eight-step
proof describes the generic comparison in the imported module, rather than this local
arithmetic specialization. Its route is retained by using the existing comparison
unchanged. The annihilator can be chosen explicitly as the coefficient prime to the
level-th power; no extra intermediate statements or definition repairs are necessary.
The arithmetic argument also works at level zero (the zero quotient); the existing
positive-level hypothesis and all statements are retained.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
