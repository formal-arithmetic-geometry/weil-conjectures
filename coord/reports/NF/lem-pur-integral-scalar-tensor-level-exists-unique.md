## Worker report

The node is already stated by the published project declaration
`WeilConjectures.scalarTensorLevel_existsUnique` in
`Sheaf.Paper.IntegralOperationsScalarComparisonModels`.  No Lean module is added.
The sandbox node records this declaration with `existing: true`.

The declaration is under section variables
`l : ℕ` with `[Fact l.Prime]`, finite-dimensional field extensions `E` and `L`
of `ℚ_[l]`, and an algebra embedding `ι : E →ₐ[ℚ_[l]] L`.  Its explicit
parameters are a scheme `W` and natural number `n`; the source finite level uses
`integralOperationsTensorLevel l E W n` and `integralOperationsTensorLevel l L W n`.
The source coefficient level is indexed by `n` and its coefficient rings use
exponent `n + 1`, exactly as required by the node.

The theorem statement is

```lean
∃! α : integralOperationsTensorLevel l E W n ⋙
    (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
  ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      integralOperationsTensorLevel l L W n,
  scalarTensorLevelNormalization l E L ι W n α
```

This renders every clause of the node.  The source type is ordinary scalar
extension applied to the finite E-level total tensor complex, and the target is
the L-level total tensor of the two scalar-extended complexes.  A component is
a chain map in the category of complexes, hence is L-linear.  The natural
transformation is natural in both complex variables because its domain and
codomain are functors from the product category.  The predicate
`scalarTensorLevelNormalization` quantifies over all complexes `P,Q`, degrees
`p,q`, site objects `U`, and sections `x,y`; it states exactly that the map sends
`1 ⊗ ((1 ⊗ x) ⊗ (1 ⊗ y))` to
`(1 ⊗ (1 ⊗ x)) ⊗ (1 ⊗ (1 ⊗ y))` in the `(p,q)` total-degree summand.
The existential uniqueness is uniqueness of this natural chain-map
transformation.  No flatness, K-flatness, boundedness, constructibility, or
invertibility assumption occurs in the theorem.

Dependency declarations used by the existing source and the node record:

- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `def-weil-completed-integral-coefficients`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` in
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
- `def-pur-change-of-rings-complex`: `SheafOfModules.changeOfRingsComplex` in
  `Sheaf.Algebra.Homology.ChangeOfRingsComplex`.
- `def-pur-sheaf-tensor-product`: `SheafOfModules.cochainModulesMonoidal` in
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `def-sfb-scalar-extension-pure-tensor-section`:
  `SheafOfModules.scalarExtensionRingIsoTmul` in
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`.
- `lem-pur-integral-operations-well-defined`:
  `WeilConjectures.integralOperationsWellDefined` and the listed finite tensor
  constructions in `Sheaf.Paper.IntegralOperationsWellDefined`.
- `def-pc-tensor-complex-sheaves`: `CochainComplex.mapBifunctor` in
  `Mathlib.Algebra.Homology.BifunctorShift`, with the recorded monoidal
  instances.
- `def-pc-sheaf-restrict-scalars`: `SheafOfModules.restrictScalars` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `def-weil-integral-scalar-extension`:
  `WeilConjectures.integralScalarExtensionOfUniverses` in
  `Sheaf.Paper.IntegralScalarExtensionUniverses`.
- `def-weil-l-adic-coefficient-extension`:
  `Padic.finite_coefficientExtensionRing` in
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.

Edge cases checked against the source statement and reviewed split: `n = 0`
(which gives exponent `n+1 = 1`), identity and ramified embeddings, zero
complexes, the empty scheme, and unbounded cochain complexes.  The theorem has
no boundedness or flatness hypotheses and remains meaningful in all these
cases.

Searches made:

- `msearch.py ... leanfinder "Unique natural scalar extension comparison for the finite quotient total tensor complex of two sheaves"`: generic sheafification, tensor, and homological-complex results only; no matching theorem.
- `msearch.py ... loogle "scalarTensorLevel_existsUnique, integralOperationsTensorLevel, scalarTensorLevelNormalization"`: no hit; the project declaration is outside Mathlib.
- `msearch.py ... grep "scalarTensorLevel_existsUnique|scalarTensorLevelNormalization" Algebra/Category/ModuleCat`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`: found the exact theorem and predicate at lines 201–240 of `Sheaf/Paper/IntegralOperationsScalarComparisonModels.lean`.
- `grep -rl` over `dag/nodes`: found this item and its parent finite-comparison node as citers; no separate competing definition was found.

No statement correction, new node, dependency module, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
