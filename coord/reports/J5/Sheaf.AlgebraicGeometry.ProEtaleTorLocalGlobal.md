## What changed

Filled `AlgebraicGeometry.Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`
with a complete proof. The proof restricts bounded flat coefficient models along the
exact slice functor, compares restricted tensor homology using exact K-flat restriction
and the natural slice tensor isomorphism, and proves the converse by a finite pro-etale
refinement of the terminal object followed by sectionwise sheaf zero detection. Unused
imports from the original plan were removed. Added local proof elaboration settings
and recorded their unchanged consumer effects in
`coord/changes/proetale-tor-local-global-proof-commands.md`. The target declaration and the
`coefficientModelSliceRestriction` definition were unchanged.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`.
There are no `sorry` declarations left in the item and no new split-off declarations.

## No longer needed

The proof does not need the original imports
`Sheaf.CategoryTheory.LocalizedModuleExactIndependent`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.CategoryTheory.SiteTorIntervalRestriction`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`,
`Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, or
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`. The corresponding exactness and restriction facts still needed are supplied by
`RingedDerivedRestrictionGeneral`, which remains a public import. The unused planned
proof dependencies are `def-pur-localized-ringed-site`, `lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-sf-site-tor-interval-restriction`, `def-weil-pbc-sites-and-cohomology`,
`def-weil-pbc-ringed-site-derived-restriction`, and
`lem-weil-pbc-site-derived-tensor-descent`. Some also remain statement dependencies;
this is pruning of the proof route, not a claim that the entire library no longer
uses them. The proof instead uses the existing bounded flat-model,
slice restriction, exact K-flat restriction, slice tensor naturality, pro-etale site,
quasi-compactness, and Tor-amplitude declarations listed in the copied DAG metadata.

## Where the brief, the DAG or earlier work was wrong

The DAG's six-step route can be shortened. A finite cover of the terminal
coefficient-site object suffices: the `CoversTop` criterion then supplies the required
covering family for every object. The resulting minimum/maximum interval and the
sectionwise sheaf argument implement the local-to-global step directly, so separate
directional theorem modules and an explicit affine cover of the scheme are unnecessary.
The top-level obsolete `tool_uses` entries
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-sf-site-tor-interval-restriction`, and
`lem-weil-pbc-site-derived-tensor-descent` were pruned; `sk-def-pe-site` remains.
No statement or definition was changed.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
