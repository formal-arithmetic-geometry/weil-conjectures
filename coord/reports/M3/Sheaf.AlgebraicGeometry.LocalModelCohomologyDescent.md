## What changed

Proved `AlgebraicGeometry.ProEtale.localModel_cohomology_descent` in
`Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent`, with the statement unchanged.
The cohomology comparison is the composition of the proved source-library
`Functor.mapDerivedCategoryHomologyFunctorIso`, the given derived model isomorphism,
`DerivedCategory.homologyFunctorFactors`, and exact scalar-extension homology.
Outside the given interval, scalar homology vanishes because the middle term is zero.
The existing cover-local isomorphism criterion, applied to the zero endomorphism
after forgetting module actions, descends this vanishing. The same finitely presented
scalar modules witness the local models. The already proved `pullback_finiteConstantLocalModel` supplies models
on the identity stratum and on affine opens, giving constructibility. The cohomology
interval yields canonical t-structure boundedness and hence bounded constructibility.

The only Lean file changed is the assigned module. Four private proof imports replace
the unused proof imports; all public imports and declarations remain verbatim.
The unused-variable linter is disabled only for this declaration, preserving its
original unused hypothesis and dependent-binder names. The existing DAG node's proof,
proof dependencies and proof origin follow this route.
Its obsolete weakly-etale-stability tool approval is removed. No definitions or
statements are changed and no consumer adaptations or change records are needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.localModel_cohomology_descent`
(node `lem-sfb-local-model-cohomology-descent`).

Holes closed: 1. Holes added: 0. Holes left in delivered Lean files: 0.
No new axioms, helpers with postponed proofs, or split statements are introduced.

Validation: the whole module compiles in 6.3 seconds; the declaration with its
scoped unused-variable linter setting compiles without warnings in 6.1 seconds.
`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` and inherited
`sorryAx`. The latter is already present in `pullback_finiteConstantLocalModel`'s
transitive dependencies, despite that theorem having a complete proof body. The
other directly checked comparison, cover-conservativity, finite-model-equivalence,
trivial-stratification and t-structure lemmas use only the three standard axioms.
Thus this is a complete proof from the existing stated library dependencies,
not a claim that the entire downstream development is already axiom-free.

## No longer needed

Removed private proof imports:

- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`
- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Mathlib.Topology.Constructible`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`

The last four modules' ingredients remain available through public dependencies;
removing their redundant direct imports does not remove those ingredients.

The following former direct proof dependencies are unnecessary on this route:
`lem-sfb-condensed-localization-exact-cohomology`,
`lem-sfb-coefficient-sections-localization`,
`lem-pur-site-restriction-module-adjunction-exact`,
`def-pur-localized-ringed-site`, and `def-weil-pbc-sites-and-cohomology`.
Their sectionwise module-category reconstruction is replaced by the already proved
internal-module exactness and generic derived-cohomology comparison, together with
source-library cover conservativity. The proof does not directly require the
coefficient-sections theorem or its large proof module.

The obsolete `sk-lem-pe-weakly-etale-stability` entry of `tool_uses` is removed:
the source-library localization comparison already encapsulates that infrastructure.
The recorded `def-constructible-stratification` notion is still used conceptually,
through the existing stronger `Scheme.Stratification.trivial`; its separate
`FiniteLocallyClosedStratification` module is not needed. Affine restriction uses
the proved finite-constant-model pullback theorem rather than reconstructing scalar
matrices again. No module or declaration is withdrawn; these are pruning statements
about this item's direct needs, not claims of whole-library unreachability.

## Where the brief, the DAG or earlier work was wrong

The expanded DAG route needlessly rebuilds a sectionwise ringed-module equivalence
and its derived cohomology comparison. The adopted source library already proves
the needed comparison for the actual exact `CondensedRing.upperStar`, so the
statement can be proved with no dependency on the newly stated localization theorem.
All local-model, cover-descent, affine-local and boundedness steps remain present;
the unit and chapter route are preserved.

The argument works without using the supplied compactness, finite-index or ordered-
interval hypotheses. They remain unchanged in the theorem. Empty covers are handled
by the sheaf-local isomorphism criterion; no cover index or geometric point is chosen.
Zero coefficients and empty schemes require no special exclusion. The affine-local
branch does not assume quasi-separatedness.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
