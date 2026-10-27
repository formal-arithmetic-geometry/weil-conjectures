## What changed

Filled the five theorem proofs in `Sheaf.Paper.ConstantCoefficientObjectsConstructible`.
Finite coefficients use the existing finite locally free line models and single-complex
support calculation. A proved private sheafification comparison transports the constant
regular-module germ equivalence to the actual regular ring sheaf.

Integral reductions use the regular K-flat representative from
`ConstantScalarStrictUnit`, its multiplication isomorphisms, and the normalized derived
scalar/restriction adjunction to identify the specified reduction map. The existing
regular-completeness calculation and the legacy/intrinsic completeness equivalence
supply both recorded membership predicates and the common interval [0,0].

Integral scalar extension uses the strict scalar-unit quasi-isomorphism and the
published good-representative comparison. Rationalization maps that isomorphism to the
rational category. The common-stage morphism is a composite of the stage identification,
the image of this isomorphism, and the inverse stage identification.

Only theorem proofs, proved private helpers, proof imports, and the existing node's
proof record change. All public signatures and coefficient-object definitions stay
unchanged. No new statements or modules are introduced.

## Proved and sorry left

Original holes closed (5):
- `WeilConjectures.finiteConstantCoefficient_constructible`
- `WeilConjectures.integralConstantCoefficient_constructible`
- `WeilConjectures.integralConstantCoefficient_scalarExtension`
- `WeilConjectures.rationalConstantCoefficient_scalarExtension`
- `WeilConjectures.AlgebraicallyClosedCoefficients.constantCoefficientPair_stageIndependent`

Holes added: zero. Sorries left in the delivered module: zero.
Existing dependency statements are used as recorded in the DAG; none is copied as a
new assumption. Private helpers are proved.

## No longer needed

Removed redundant proof imports:
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`

Their relevant results are either supplied by the recorded strict-unit dependencies or
replaced by finite locally free line models and the single-support theorem. No public
declaration is removed. No module is claimed globally unused: these modules can remain
needed by other consumers and by the retained dependencies. Both strict scalar-unit
nodes remain needed. No new proof branch bypasses the blueprint unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The theorem node currently attaches its
Lean record to `ConstantCoefficientScalarNormalization`, which supplements the older
five declarations in the assigned module. This delivery preserves that attachment and
updates only the shared proof account to record the implementation here.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
