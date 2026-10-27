## What changed

In `Sheaf.Paper.DerivedPullbackTensorIso`, proved
`WeilConjectures.canonicalCommonStagePullbackTensor_braiding_spec` by representing
both routes at one finite coefficient stage. Five proved private helpers establish
integral braiding naturality through faithful coherent reduction and rational
braiding naturality by bilinear localization. The generic localization calculation
follows the existing private helper in `LocalizedTensorBraidingNaturality`; importing
that module here would create a cycle. A generic categorical helper cancels the
comparison isomorphisms without unfolding the large sheaf constructions.
All public signatures and imports are unchanged.
The categorical calculation names the finite-stage category instances explicitly.
The stage-category wrapper has the same scoped reducibility setting already used
by `DerivedPullbackTensorHom`; this preserves transparency and kernel checks.
Local irreducibility settings keep standard derived-category, coefficient-linearity,
and chosen constraint constructions from expanding during elaboration. The category
settings are applied after constructing the unit evaluation map, whose additive
instance needs the original category data. Elaboration is synchronous. The main
node records this proof step. No definition bodies or other modules changed.
The complete module compiled through `lcompile.py` in 48.7 seconds with no errors.

## Proved and sorry left

Closed 1 of the original 9 holes:
`WeilConjectures.canonicalCommonStagePullbackTensor_braiding_spec`.
Added 0 holes; split off 0 statements. Eight original holes remain, all attached to
`lem-pur-derived-pullback-tensor-iso`:

- `WeilConjectures.pullbackTensorCommonComposition_existsUnique`
- `WeilConjectures.pullbackTensorCommonAssociator_existsUnique`
- `WeilConjectures.pullbackTensorCommonBraiding_existsUnique`
- `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`
- `WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique`
- `WeilConjectures.canonicalCommonStagePullbackTensor_associative_spec`
- `WeilConjectures.derivedPullbackTensorIso`

## No longer needed

None. No imports, nodes or modules are withdrawn. The partial result uses the
existing object and representative normalization formulas and preserves the unit route.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. Object-equality transport must name the public
common-stage functors explicitly, since their choice definitions are locally
irreducible. The final calculation uses functor images of comparison inverse
identities and rational braiding naturality; it does not require injectivity of a
scalar-extension functor on Hom groups.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
