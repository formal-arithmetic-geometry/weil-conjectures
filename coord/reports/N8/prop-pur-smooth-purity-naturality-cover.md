## Worker report

The module `Sheaf.SecSmoothPurity.SmoothPurityNaturality` states
`WeilConjectures.PurityFiniteSetting.smoothPurityMap_naturality_choice_independence`.
It retains the finite purity setting and all hypotheses of
`thm-pur-finite-coefficient-smooth-purity`: a finite coefficient datum `P`, separated
finite-type `k`-schemes `X` and `Y`, a separated finite-type smooth morphism `f` of
relative dimension `d`, and finite-Tor constructible objects `K` and `K'`. The
proof is `sorry`, as required for stage 2.

The first conjunct is the naturality square. Its left side is
`P.smoothPurityMap f d K hK` followed by the map induced by
`P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))` on
`(sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u`, rendering the exceptional
inverse-image map `Rf^!u` after the intrinsic realization at `X`. Its right side is
the map induced by the `2*d` shift of the tensor map on
`(P.smoothPurityPullback f).obj ((sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)`,
followed by `P.smoothPurityMap f d K' hK'`; this is the derived version of
`(Lf^*u)(d)[2d]` followed by `gamma_{f,K'}`. Equality is an equality of morphisms,
not merely of isomorphism classes.

The second conjunct quantifies over two etale derived representatives `K₀`, `K₀'`
and comparison isomorphisms `e`, `e'` to the same canonical intrinsic representative
`(sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K`. It equates the two
`P.smoothPurityTensorMapInPresentation` morphisms, with the same `f`, dimension,
base map, pullback object, and exceptional target. This is the explicit
presentation-level rendering of independence of representative, compactification,
coordinate, and resolution choices in the canonical construction.

The statement dependencies used are `Sheaf.Paper.FiniteCoefficientSmoothPurity`,
which supplies `isIso_smoothPurityMap` and the exact finite-purity hypotheses, and
`Sheaf.Paper.SmoothPurityMap`, which supplies `smoothPurityMap`,
`smoothPurityTensorMapInPresentation`, `smoothPurityExceptionalOver`, the intrinsic
pullback, and the canonical reassociation. The proof dependencies named by the DAG
were read: `Sheaf.Paper.CohomologicalSmoothnessComparison`,
`Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`,
`Sheaf.Paper.CohomologicalSmoothnessTheorem`,
`Sheaf.Paper.PbcCoefficientTwists`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution`,
`Sheaf.Paper.PurityDiagonalDualizingObject`, `Sheaf.Paper.PurityDncInvariance`,
`Sheaf.Targets.VectorBundlePurity`, and
`Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`. The Mathlib leaves
`fix-prop-projection-formula`, `def-pc-tensor-complex-sheaves`, and
`lem-weil-pbc-finite-type-over-noetherian` were also checked through their recorded
matches; no duplicate declarations were introduced. The proof-only cohomological
smoothness import is omitted because its module has a known duplicate declaration
when imported alongside the published map module; the statement itself needs only
the two recorded statement-dependency modules.

Edge cases checked are `u = 0`, `u = 𝟙 _`, `K = 0`, `d = 0`, `n = 1`, a ramified
finite extension, and an empty source scheme. Each reduces to the corresponding
zero/identity map or to the zero sheaf category; the shift expression remains
well-typed at `d = 0`, and the finite-Tor predicate retains the required `n ≥ 1`
hypothesis. Two distinct presentations are permitted even when their underlying
objects are isomorphic only through the supplied comparison arrows; no arbitrary
orientation is quantified.

Searches for an existing declaration were made as follows. `msearch.py ...
leanfinder "smooth purity map natural in coefficient complex independent of choices"`
returned only standard-etale and algebraic smoothness declarations, with no purity
map. `msearch.py ... loogle "IsIso smoothPurityMap naturality DerivedCategory"`
returned no hits (the query's `IsIso` identifier is not known to that service).
`msearch.py ... grep "smoothPurityMap|smoothPurity.*naturality" Mathlib/AlgebraicGeometry`
returned zero hits. Grepping `WeilConjectures/` found only the older
`AlgebraicGeometry.Etale.smoothPurityIso`, whose arbitrary input isomorphisms do not
state naturality or choice independence. Grepping `lean/Sheaf` found only the
canonical map definition and its finite-coefficient isomorphism theorem. The
Mathlib search records already attached to the node likewise found no exact match.

No `STATEMENT-DISPUTED` flag or node correction is needed.

## Second reading by N8

I reread the node statement, the two statement dependencies, and the complete module.
The finite coefficient setting, scheme-over-`Spec k` instances, separated and
locally-finite-type hypotheses, quasi-compactness, smooth relative dimension, and
finite-Tor hypotheses for both `K` and `K'` are all explicit. The naturality clause
uses the exceptional functor map on the left and the shifted tensor pullback map on
the right, with composition in Lean's left-to-right categorical order, so it matches
`Rf^!u ∘ gamma_K = gamma_K' ∘ (Lf^*u)(d)[2d]`. The independence clause compares
exactly the presentation composites used to define the canonical tensor map and
keeps the same intrinsic object and target on both sides. I checked that the map
orientation is `smoothPurityMap f d K hK` followed by the exceptional map, while the
other side starts with the shift/tensor map and ends with `smoothPurityMap f d K' hK'`.
The module compiles cleanly with `scompile.py`; no hypothesis or conclusion was
added beyond the two clauses rendering the proposition.
