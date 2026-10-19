## Worker report

The node is already stated exactly by the existing declaration
`AlgebraicGeometry.AffineBlowup.homogeneousAwayToChart_injective` in
`WeilConjectures.Blowup.Affine.ChartAlgebra`; therefore no Lean module is added.
The declaration is the theorem

```lean
theorem homogeneousAwayToChart_injective :
    Function.Injective (homogeneousAwayToChart I ha) :=
```

Its surrounding context binds `{A : Type u}`, `[CommRing A]`, `I : Ideal A`,
`a : A`, and `ha : a ∈ I`. Thus `homogeneousAwayToChart I ha` is precisely the
constructed homogeneous-localization chart map θ_a, and the conclusion is its
injectivity. Every clause of the node statement (“the constructed map θ_a is
injective”) is represented by `Function.Injective (homogeneousAwayToChart I ha)`.
There are no statement dependencies. The proof dependencies named by the node
are the existing chart-fraction equality and chart-map declarations in the same
published module; they are used by the existing theorem's proof.

Edge cases checked: `a` is allowed to be any element of `I`, including `a = 0`;
`I` may be the zero ideal; and `A` may have zero divisors. The source proof uses
localization equality without cancellation, so these cases remain covered.

Searches made:

- `msearch.py ... leanfinder "injectivity of homogeneous localization map to affine blowup chart"` returned Mathlib candidates but no exact chart-map declaration.
- `msearch.py ... loogle "homogeneousAwayToChart, Function.Injective"` returned no hits (the project declaration is not in Mathlib).
- `msearch.py ... grep "homogeneousAwayToChart_injective" WeilConjectures` found the exact declaration and its uses in `lean/WeilConjectures/Blowup/Affine/ChartAlgebra.lean`.
- `rg` over the project and DAG confirmed the exact published declaration and its audit record; no competing definition exists.
- `scompile.py --source WeilConjectures.Blowup.Affine.ChartAlgebra` retrieved the source and confirmed the full theorem signature and docstring.

No new nodes, dependency modules, statement correction, or `STATEMENT-DISPUTED` issue is present.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
