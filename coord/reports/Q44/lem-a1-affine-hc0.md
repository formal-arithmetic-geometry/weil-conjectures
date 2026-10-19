## Worker report

The node is already stated by the published source declaration
`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero` in
`WeilConjectures.WeilSheaf.Curve`. No module is added. Its formal statement is
`Subsingleton (F.compactlySupportedCohomology 0).carrier`, the categorical zero
form of `H_c^0(U,F)=0`.

The declaration's binders render each clause of the node statement: the ambient
finite-field, coefficient-prime, separated, locally finite type, quasi-compact
scheme binders in the source module provide the chapter setting; `[IsAffine U]`
renders affine; `[SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]`
renders a smooth relative-dimension-one curve; `[GeometricallyConnected
(U ↘ Spec (CommRingCat.of k₀))]` renders geometric connectedness; `F :
WeilSheaf k₀ l U` is the Weil sheaf; `hF : F.IsLisse` is lissity; and
`Subsingleton (F.compactlySupportedCohomology 0).carrier` is the degree-zero
compact-support vanishing. The source docstring explicitly identifies the
geometric base change as the scheme denoted `U` in the blueprint.

Dependency declarations consulted:

- `WeilConjectures.ordinaryCompactCohomology` from `Sheaf.Paper.OrdinaryCompactCohomology`.
- `WeilConjectures.sfWeilComplex` from `Sheaf.Paper.SfWeilSheafComplex`.
- `AlgebraicGeometry.Scheme.LisseIntegralSheaf` from `Sheaf.Paper.LisseAdicSheaves`.
- `RealSheaves.Setup` from `Sheaf.Paper.RealSheavesSetup`.

The existing source declaration was checked in full, including its docstring and
signature, via `scompile.py --source WeilConjectures.WeilSheaf.Curve`. It is the
same lisse Weil-sheaf compact-support vanishing statement, so the node records
`existing: true` and no duplicate declaration is written.

Edge cases checked from the source assumptions and theorem shape: the zero
sheaf is allowed; `Subsingleton` correctly expresses zero even when the carrier
is empty; the affine hypothesis excludes the proper smooth connected curve case;
and degree is the integer `0` used by `compactlySupportedCohomology`.

Searches made:

- `msearch.py ... leanfinder "compactly supported cohomology degree zero lisse Weil sheaf smooth geometrically connected affine curve"`: no exact match in Mathlib; unrelated cohomology hits only.
- `msearch.py ... loogle "WeilSheaf.compactlySupportedCohomology, WeilSheaf.IsLisse"`: no hits (unknown identifier in Loogle).
- `msearch.py ... grep "subsingleton_compactlySupportedCohomology_zero|compactlySupportedCohomology" WeilConjectures/WeilSheaf`: found `WeilConjectures/WeilSheaf/Curve.lean`, including the exact declaration.
- `rg` over `WeilConjectures` and `lean/Sheaf`: found the source declaration in `WeilConjectures.WeilSheaf.Curve`; no project duplicate.

No `STATEMENT-DISPUTED` flag and no node fault.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
