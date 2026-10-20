## What changed

Proved `SheafOfModules.exists_strictPerfect_model_in_tor_window` with its original signature and public imports. The proof constructs upper-bounded strict-perfect charts by local splitting, then good lower truncations using the flat finitely presented opcycle. Added fully proved support modules for exact restriction, finite-projective local lifting, upper shortening, opcycle retractions and lower shortening. The opcycle proof includes the categorical Tor diagram chase and an explicit finite presentation matrix; it does not assume global sections preserve epimorphisms or that the site has binary products.

All six modules compiled together through `lcompile.py --all`. Later preflight compiles exposed expensive concrete slice-functor unfolding. General private pushforward preservation helpers avoid that unfolding; the final opcycle module compiled cleanly in 13.3 seconds. No time limit was raised and no module was split for performance. Every new definition has an explicit construction and contains no sorry. Choices of local ranks and splittings occur only inside proofs of existence, not hollow public data definitions. New restriction comparisons are canonical universal-property comparisons.

## Proved and sorry left

Closed the original one hole in `SheafOfModules.exists_strictPerfect_model_in_tor_window` (1 of 1). Added zero holes; zero split-off unfinished statements. There are no `sorry`s in any delivered Lean file. New public lemmas and constructions are all proved, including `exists_strictPerfect_upper_model`, `exists_strictPerfect_lower_model`, `exists_local_retract_opcycles_of_perfect_tor`, `transport_slice_retract`, the restriction APIs, and the two local lifting lemmas. Existing declared dependencies such as `torAmplitude_iff_exists_bounded_flat_model`, `wfSiteDerivedTensor_first` and `exists_local_finiteFree_retract_of_flat_of_finitePresentation` are used as authorized by stage 3 and are not changed.

## No longer needed

The main theorem now imports only the bounded-flat-model theorem and the upper/lower model modules for its proof. Removed its former proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.KFlat`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.SiteTorIntervalRestriction`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`

The direct dependency nodes of the main theorem are now `lem-sp-ringed-site-tor-flat-model`, `lem-sf-site-perfect-upper-model`, and `lem-sf-site-perfect-lower-model`. Its former cone/resolution dependencies are handled by the existing first-variable tensor comparison and bounded-flat-model theorem rather than repeated in the main proof. The original `lem-sf-site-tor-interval-restriction` and `lem-weil-pbc-site-flat-opcycles-tor-criterion` interfaces specialize to equal site universes; the proof establishes the independent-universe cases internally from the existing equational criterion, categorical diagram chase and bounded flat model. The flat-finite-presentation local-retract theorem remains used by the boundary lemma. No blueprint unit route is bypassed (the item's unit has empty realized statement/step lists). No whole module is claimed globally pruned without checking other consumers.

Removed direct proof-dependency edges (some remain below the bounded-flat-model or tensor comparison theorem):

- `lem-sf-site-tor-interval-restriction`
- `def-weil-pbc-strict-perfect-coefficient-package`
- `def-pc-flat-sheaf-modules`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-pc-kflat-resolution`
- `lem-pur-quasi-iso-cone-acyclic`
- `def-pc-kflat-complex`
- `lem-pc-tensor-mapping-cone-iso`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
- `lem-pur-site-restriction-module-adjunction-exact`
- `def-pur-localized-ringed-site`
- `lem-weil-pbc-site-flat-opcycles-tor-criterion`
- `lem-sf-site-flat-fp-finite-retract`

Removed obsolete top-level `tool_uses` approvals for the former direct route:

- `lem-pur-quasi-iso-cone-acyclic`
- `lem-pc-kflat-resolution`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-site-flat-opcycles-tor-criterion`
- `lem-pc-tensor-mapping-cone-iso`

## Where the brief, the DAG or earlier work was wrong

The supplied Tor-restriction and opcycle-flatness interfaces do not directly match the independent site universes of the assigned statement. This delivery proves the required general cases internally. Finite-free sheaves need local lifting; they are not assumed categorical projectives. The generic global-presentation-to-local-presentation convenience theorem assumes binary products of the site; the delivery instead constructs the quasi-coherent presentation datum directly using exact restriction preserving all colimits, so no additional hypothesis is added.

Previous compile connectivity failures and repeated provider interruptions were recovered without a duplicate delivery. No delivery had begun when this resumed work started. Dispatcher reference-clock resets were observed during resumed attempts; no budget metadata was edited. The unchanged source statement and five target signatures remain intact.

## New nodes

`lem-sf-site-perfect-restriction-exact`: Compare restriction with abelian sheaf restriction under the faithful forgetful functors. Presheaf evaluation proves finite-limit preservation. The cocontinuous sheaf adjunction proves finite-colimit preservation. Forgetting modules reflects the universal properties.

`lem-sf-site-perfect-overmap-exact`: Use the same forgetful comparisons for the continuous and cocontinuous functor Over.map. Finite limits and colimits are preserved and reflected under the abelian sheaf comparison.

`lem-sf-site-perfect-restriction-additive`: Module maps restrict componentwise. Both sides of the additive-functor equation agree on every section.

`lem-sf-site-perfect-overmap-additive`: Further restriction acts on each component of a module morphism. Evaluate both sides on an object and a section; the equality is reflexivity.

`lem-sf-site-perfect-overmap-comp`: Compose the module pushforward comparison with the natural isomorphism Over.mapComp and the induced ring-map comparison. The latter agrees sectionwise by associativity.

`lem-sf-site-perfect-derived-restriction-iso`: Exactness supplies the induced derived functor. Use mapDerivedCategoryFactors at the chosen representative, then apply the derived functor to its canonical isomorphism with E.

`lem-sf-site-perfect-package-map`: Map each of the displayed retraction arrows under the additive functor. Conjugate with its preserved finite-product comparison and the unit isomorphism. Functoriality carries the splitting equation to the splitting equation.

`lem-sf-site-finite-projective-lift`: Forget the epimorphism to abelian sheaves and use local surjectivity at the terminal object of the slice for each finite generator. Intersect their covering image sieves. Extend the lifted sections naturally over each new slice, assemble them using the preserved biproduct colimit, and verify the required equation on all coprojections.

`lem-sf-site-finite-projective-section`: Apply finite-free local lifting to the retraction from the finite free sheaf, identified with the finite biproduct. Compose its lift with the displayed inclusion of the target. The splitting equation follows from the lifting equation and the original retraction.

`lem-sf-site-perfect-upper-model`: Start on a strict-perfect chart. By descending induction from a term bound, construct locally finite-free retractions for cycles: exactness makes the map onto the next cycles epic, local finite-projective lifting splits it, and 1-fs factors through the kernel. Compose the finite covering refinements. The good upper truncation at b has these cycles in degree b, unchanged lower terms and zero higher terms. Its canonical map is a quasi-isomorphism since cohomology vanishes above b. Exact restriction and the successive restriction comparisons identify its derived object with the required restriction of E.

`lem-sf-site-perfect-opcycles-retract-transport`: Push the retraction along the inverse of the iterated-slice equivalence. This functor preserves finite limits through the presheaf forgetful comparison and sends the unit to the unit. Conjugate the mapped retraction by the finite-product comparison and the definitional comparison with overMap. The splitting equation follows by functoriality.

`lem-sf-site-perfect-opcycles-retract`: Use the bounded flat model to restrict the Tor interval; the local equational criterion proves that flatness restricts at independent universes. Finite-free retract terms are dualizable and flat, so the bounded complex is K-flat. The first-variable tensor comparison and the degree-zero tensor isomorphism prove universal exactness in degree a-1. The categorical Tor diagram chase proves the opcycles flat. Construct a finite global presentation explicitly with matrix (1-ip, i d q), checking its cokernel universal property. Restriction preserves colimits, hence this gives local finite presentations without binary products on the site. Apply the declared flat finitely presented local-retract theorem on the slice and transport its retract along the iterated-slice equivalence. The terminal-slice covering is a covering of U.

`lem-sf-site-perfect-lower-model`: Restrict a bounded flat model of E exactly to show that the chart has no cohomology below a. Locally the opcycles in degree a are a finite free retract by the boundary lemma. Apply the good lower truncation after restriction. Its degree-a term is the opcycle, higher terms retain the finite-free splittings and lower terms vanish. The canonical map is a quasi-isomorphism by the cohomology bound. The inequality a<=b retains the upper term bound. Derived restriction and composition comparisons identify the resulting representative with E on the new slice.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
