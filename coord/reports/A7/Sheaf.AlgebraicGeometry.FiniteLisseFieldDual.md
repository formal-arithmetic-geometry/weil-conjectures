## What changed

The signatures of `AlgebraicGeometry.Etale.finiteLisseFieldDual` and
`finiteLisseDualPullbackComparison` are unchanged. The comparison definition is
refactored through the source strong-monoidal Hom comparison; a proved generic
transpose identity checks that it is the same canonical map. The theorem now has a
complete Lean proof from a local perfect model and a strictly smaller cohomology lemma.
The proof constructs the finite-lisse assertion using the existing ordinary sheaf-dual
theorem. Its pullback assertion is proved for the actual canonical morphism: a private,
proved helper identifies it with the strong-monoidal internal-Hom comparison followed
by the mapped unit comparison. The helper accepts arbitrary second objects to avoid
comparing different concrete presentations of the derived monoidal unit. A private
coefficient-ring lemma freezes this comparison before specialization to the lifted
prime field. The complete item compiled without warnings in 32.4 seconds. In a separate
consumer check it compiled in 37.5 seconds and its unchanged direct consumer
`SmoothGenericDirectImage` compiled against it in 9.4 seconds. No forced consumer
adaptation is needed.

`FiniteLisseFieldSitePerfect` is a new, proved module. It applies the first clause of
`finiteRing_derived_local_constancy`, chooses bases in the finite field modules, maps
the resulting isomorphisms through the constant-sheaf functor, and supplies the exact
pullback comparison. No new local-model existence hole remains.

`FiniteLisseFieldDualHomology` states the remaining local linear-algebra calculation
for prime-field coefficients on any site-perfect etale complex.
The predicate is the existing ordinary-etale predicate in the source library; both new
DAG statements explicitly spell out its covering, bounds, and finite-free retract data.
No completed, integral, rational, or pro-etale perfectness predicate is substituted.

The parent node records this route. Proof-only imports are private imports. Retired
re-export modules and the unused ringed-site proof imports are removed. The direct
consumer `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` explicitly imports its own
derived-category, bounded-constructibility and ringed-internal-Hom interfaces.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Etale.finiteLisseFieldDual`
(node `lem-fin-lisse-field-dual`), by a complete proof from named statements.
The item has zero remaining holes. Also proved the new theorem
`AlgebraicGeometry.Etale.finiteLisseField_sitePerfect`
(node `lem-fin-lisse-field-site-perfect`) and the private canonical-comparison helper.

Added one hole: `AlgebraicGeometry.Etale.sitePerfect_fieldDual_homology`
(node `lem-fin-lisse-field-dual-homology`). This is one closed upper hole and one added
lower hole, hence a decomposition, not a net hole elimination. The remaining theorem
needs the canonical homology-evaluation map, the exact constant-sheaf comparison
on bounded finite-free complexes, and descent of the resulting field-linear
isomorphisms. Its docstring supplies
the full mathematical argument. The remaining proof stays in coefficient-module
sheaves: exact strong-monoidal constant sheaves transfer the local module duality
calculation, and evaluation provides the compatible global comparison. It asserts no pullback theorem and no finite-lisse
preservation theorem. Existing imported declarations may themselves contain `sorry`;
none has been modified or copied into this delivery.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Homology.DerivedInternalHom`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.Algebra.Homology.HomComplex`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

`Sheaf.AlgebraicGeometry.DerivedCategories` is replaced by its source module.
`WeilConjectures.ConstructibleSheaf.Monoidal` is now a proof-only import; the public
statement uses `ConstructibleSheaf.Defs`.

The parent no longer follows the K-injective slice-restriction, ringed Hom-complex,
truncation-triangle, or pullback-by-truncation proof. All original direct proof
edges and their old top-level tool approvals are removed:

- `def-pur-derived-internal-hom`
- `lem-pur-kinjective-restrict-localized`
- `def-pur-sheaf-hom`
- `def-pur-hom-complex`
- `def-weil-size-convention`
- `def-weil-pbc-constructible-complexes`
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`
- `def-sbc-standard-tstructure-derived-category`
- `lem-sf-derived-truncation-triangle`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-sf-derived-homology-long-exact`
- `def-weil-pbc-derived-categories`
- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-pur-kinjective-resolutions-exist`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `def-weil-pbc-inverse-image`

A read-only import-graph comparison against `TargetsCheck` removes exactly two
modules from the current targets' import closure:
`Sheaf.Algebra.Homology.RingedInternalHomExactRestriction` and
`Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`.
The comparison also adds the local-model theorem and its dependencies, plus the two
new modules; it is not a claim of fewer total imports.

This lists removed direct edges, not a claim that every such module disappears from
the entire targets' import closure. The remaining cohomology calculation uses
the exact strong-monoidal constant-sheaf functor on bounded finite-dimensional
module models, avoiding the ringed bounded-free RHom and restriction interfaces.
The local-model theorem has its own existing dependencies. The new
route uses only the local-model clause of finite-ring derived local constancy; its
Hom-sheaf, isomorphism-sheaf and connected-fibre clauses are not used.

## Where the brief, the DAG or earlier work was wrong

The original direct proof imports implement ringed-site `SheafOfModules`, whereas
the item's actual RHom is the source library's closed derived Hom for
`Sheaf T.smallEtaleTopology (ModuleCat Lambda)`. Applying the former declarations
directly would require an additional bridge. The source library already proves
site-perfect dualizability and strong-monoidal Hom comparison in the latter encoding.
The existing finite-ring local-constancy statement also already supplies the local
constant models needed here. These facts allow the replacement route without
changing the mathematical statement. The unit record has no realized substeps
requiring the abandoned below-unit route.

Zero coefficients are excluded by primality; zero ranks, zero complexes and the empty
scheme are included. The prime-field theorem retains its invertibility hypothesis,
although neither of the two helper statements needs it. The cohomology helper retains the prime-field coefficient presentation of the
parent. An unnecessary generalization to arbitrary fields was removed.

## New nodes

`lem-fin-lisse-field-site-perfect` attaches the proved local-perfect-model theorem.
It is proved from the already stated finite-ring local-constancy theorem; its field
linear algebra is a basis isomorphism followed by a constant-sheaf functor.

`lem-fin-lisse-field-dual-homology` is the sole remaining split. It isolates the
cohomology-dual calculation for site-perfect field complexes, strictly below the
three-clause parent theorem. It has its own module, source and full proof in words,
with real LeanSearch, LeanFinder, Loogle and Mathlib source searches recorded in
searches.jsonl. Both new nodes record all three required kinds of search.
Blueprint searches found `lem-pod-cohomology-of-dual-over-field`, the already
proved module-category calculation used in the new homology node; it does not
state the sheaf result. Searches for bounded finite locally constant complexes
and tag 094G found no further blueprint duplicate.
Change record: `coord/changes/finite-lisse-field-dual-comparison.md`. It records
the performance problem, old and new definitions, the transpose identity, and
all transitive consumers. No external module is adapted.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
