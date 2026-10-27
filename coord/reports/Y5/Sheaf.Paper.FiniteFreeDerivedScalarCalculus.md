## What changed

Replaced the sole sorry in `AlgebraicGeometry.finiteFreeDerivedScalarCalculus` with a
complete assembly from two strictly smaller scalar-calculus statements. The proof has
three proved private helpers: `scalar_tor_amplitude`, `scalar_etale_constructible`, and
`scalar_proetale_constructible`. The first uses arbitrary degree-zero B-module sheaves,
the derived balancing comparison, exact restriction/single-functor compatibility, and
faithful exact restriction's reflection of cohomology concentration. The second applies
`constructibleCoefficientSheaf` to each cohomology sheaf and preserves the original
cohomological bounds. The third transports the etale origin through the existing
coefficient/comparison square using `mapDerivedCategoryCompIso` and
`mapDerivedCategoryNatIso`.

Extracted all 11 original data, structure, definition and instance declarations verbatim
into `Sheaf.Paper.FiniteFreeScalarCalculusData`, publicly reexported by the original
module. This is necessary to avoid an import cycle with the intermediate theorem modules.
It is not a response to a compile timeout. A parser comparison confirms all 12 original
signatures are identical and all 11 data/structure/instance bodies are identical. The
original theorem docstring is unchanged. No adopted source-library file is changed.

The two new theorem modules are `Sheaf.Paper.FiniteFreeScalarTensorCalculus` (ordinary
and exact derived scalar descent) and `Sheaf.Paper.FiniteFreeScalarDerivedTensorModels`
(normalized K-flat total-complex comparison). Both have complete proof descriptions and
DAG nodes. The original node records the actual assembly and the data node identifies
the extracted public interface. Change record:
`coord/changes/Y5-finite-free-scalar-calculus-data.md`.

## Proved and sorry left

Original holes closed: `AlgebraicGeometry.finiteFreeDerivedScalarCalculus` (node
`lem-sf-finite-free-derived-scalar-calculus`), 1 of 1. Its proof is complete relative to
the named intermediate statements. Its module now has zero sorry.

Holes added, two:

- `AlgebraicGeometry.finiteFreeScalarTensorCalculus`, node
  `lem-sf-finite-free-scalar-tensor-calculus`: exact descent, localized normalized scalar
  adjunction and basis decomposition, conservativity, K-flat extension and ordinary
  balanced tensor comparison; no derived tensor comparison, constructibility or Tor bound.
- `AlgebraicGeometry.finiteFreeScalarDerivedTensorModels`, node
  `lem-sf-finite-free-scalar-derived-tensor-models`: the natural normalized derived tensor
  comparison, assuming the ordinary scalar package; no constructibility or Tor bound.

This is a decomposition (one upper hole removed, two lower holes added), not a net
sorry-free proof of scalar calculus. The three assembly helpers contain no sorry. There
is no sorry in a definition, no private holed declaration, and no new axiom. `Nonempty`
is eliminated only in the theorem proof; no definition chooses an arbitrary witness.

## No longer needed

Removed the following proof-only imports from the item module:

- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.SecSmoothPurity.CochainInverseComparison`
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`
- `Mathlib.CategoryTheory.Localization.Adjunction`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`

The original public imports are preserved through `FiniteFreeScalarCalculusData`.
`ConstructibleCoefficientSiteSquare` remains a proof import: its proved
`constructibleCoefficientSheaf` clause is used directly, rather than the larger
bounded termwise-complex conclusion. Added a proof-only import of
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` because its
comparison theorem is not public through `ConstructibleCoefficientSiteSquare`.

The old direct dependencies for scalar descent and K-flat tensor normalization now
belong to the two intermediate nodes. They are not claimed mathematically unnecessary:
those constructions remain needed and their dependency lists are retained there.
The main node's old approved tool_uses entries (K-flat resolution, derived change of
rings, ringed K-flat pullback, cancellation, tensor descent, comparison exactness and
inverse-image tensor comparison) are removed because its assembly no longer directly
uses them. No existing module is withdrawn and no unit route is bypassed. Pruned whole
modules: none.

## Where the brief, the DAG or earlier work was wrong

Several proof dependencies use the intrinsic `SheafOfModules` presentation; this item
uses fixed-ring `Sheaf J (ModuleCat A)` with normalization in those coordinates. In
particular `nonempty_ordinaryDerivedChangeOfRings` is a theorem for ordinary ModuleCat
complexes, not this sheaf category. The existing general K-flat/cancellation theorems
do not in one application supply the requested fixed-presentation normalization. Those
bridges are recorded explicitly in the two smaller intermediate statements instead of
claiming a one-line specialization.

The larger `constructibleCoefficientSiteSquare` theorem bounds terms of a complex; the
input here only bounds cohomology, so applying that theorem to an arbitrary representative
would be wrong. The proof instead uses its proved sheaf coefficient clause on H^q and
exact-functor homology, with the existing derived comparison square for pro-etale origins.
No mathematical statement was disputed or weakened. Rank zero, B the zero ring, the
empty scheme, arbitrary unbounded representatives and nonconstructible degree-zero Tor
test sheaves all satisfy the same argument; no faithfulness of extension is assumed.

## New nodes

`def-sf-finite-free-scalar-calculus-data` records the extracted conclusion structures
and the fixed scalar functors, with unchanged formulas. Its Lean attachment is
`AlgebraicGeometry.FiniteFreeScalarCalculus` in the data module.

`lem-sf-finite-free-scalar-tensor-calculus` records the ordinary/exact-descent construction
with its basis and local-section normalization. It preserves the original steps 1-5
and ordinary balancing part of step 7 and has no bounded constructibility or derived
tensor claim.

`lem-sf-finite-free-scalar-derived-tensor-models` records steps 6-7, explicitly assuming
the preceding ordinary package and concluding the normalized derived tensor models.
Its acyclic tensor test proves K-flat restriction before localizing the total-complex
balancing maps. Both statement nodes are strictly smaller than the parent, and neither
contains the constructibility or Tor interval conclusions proved in the assembly.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
