## Worker report

The item is stated in `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`.
The comparison is an actual morphism: the adjunction mate of the realized module
scalar-extension unit, using the identity-on-constant-sections restriction comparison.
`comparisonTransformation` packages its naturality; `comparisonIso` is its associated
natural isomorphism. Scalar extension is the left adjoint of actual restriction,
which determines it uniquely with its unit. The representative comparison maps are
also actual adjunction mates, not arbitrary isomorphisms chosen after the theorem.

Hypotheses and clauses are rendered as follows.

- A small site is `{C : Type u} [Category.{v} C]` with
  `J : GrothendieckTopology C`. Neither a terminal object nor enough points is assumed.
  The coefficient universe is `max u v`, as in the recorded constant-functor interface;
  the site object and morphism universes remain independent.
- The commutative rings are `R S : Type (max u v)` with `[CommRing R] [CommRing S]`
  and `q : R →+* S`. `realizationRing` is Mathlib's constant CommRingCat sheaf.
  `restriction` uses its induced constant ring map and Mathlib's actual module-sheaf
  restriction. `realizationModules` is the existing `SheafOfModules` category.
- The unbounded categories are `DerivedCategory (ModuleCat R)` and
  `DerivedCategory (realizationModules J R)`. The four `HasDerivedCategory` sizes
  `wR wS dR dS` are independent choices of localization size, not extra mathematical
  hypotheses. No bounded subcategory occurs.
- The exact derived constants are `commutativeSiteDerivedConstantModuleFunctor`;
  its underlying termwise functor is the recorded constant module presheaf followed
  by module sheafification. The dependency transport is described below.
- The asserted natural isomorphism is `comparisonIso`, with components `comparison`.
  The first conjunct of `constantRealizationDerivedScalarExtension` says the actual
  natural transformation is invertible, in the derived category of S-module sheaves.
- Clause (1) quantifies over every integer-indexed complex `P`, with
  `P.IsKFlatForTotalTensor` and `∀ n, Module.Flat R (P.X n)`. The former is the
  already-landed binary total-tensor definition of K-flatness, equivalently the
  acyclic-total-tensor definition over modules: the mapping cone of a quasi-isomorphism
  is acyclic and total tensor commutes with cones; conversely use the map from zero
  to an acyclic complex. Symmetry makes the two tensor sides equivalent.
  Its conclusions use the recorded sheaf predicates
  `IsKFlatIndependentCoefficients` and `IsFlatOnSite` on the termwise constant complex.
  Both representative maps are invertible, and the displayed square identifies
  `comparison` with the localization of `complexComparison`.
  The independent statement `moduleComparison_tensor` says its termwise maps are
  isomorphisms and sends `s • unit(constant x)` to the constant pure tensor `s ⊗ x`.
  Thus the map is the identity of constant tensor presheaves, with the S-action;
  Mathlib's extension writes scalar first, whereas the node writes scalar second.
  A representative of an arbitrary M is handled by the naturality statement and
  transport along its isomorphism to `Q.obj P`; this adds no choice of representative.
- Clause (2) is the final conjunct: the sheaf derived unit, followed by restriction
  of `comparison` and `derivedRestrictionIso.hom`, is exactly the realized module
  derived unit. The restriction identification itself is localized from the unique
  identity-on-constant-sections ordinary comparison.
- Clause (3) is `constantRealizationDerivedScalarExtension_transitivity`.
  It binds an arbitrary third commutative ring T and ring map b, with independent
  module and sheaf localization sizes. Both transitivity isomorphisms are constructed
  by adjoint uniqueness from identity-on-sections restriction composition. The
  equation compares the routes through the two comparisons and the composite-map
  comparison. Their docstring identifies these normalized maps with the usual tensor
  associators `(x ⊗ s) ⊗ t ↦ x ⊗ b(s)t` on K-flat representatives.
- There is no flatness assumption on q or b, no boundedness, no finite generation,
  and no Noetherian hypothesis. All theorem proofs are postponed with named,
  source-labelled proof docstrings. Definition data are explicit constructions or
  chosen from unique universal properties, never arbitrary existence witnesses.

Dependency declarations used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the Grothendieck-topology
  presentation already records the site axioms.
- Mathlib `CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`,
  `constantCommuteCompose`; Mathlib module sheaves: `SheafOfModules`,
  `SheafOfModules.restrictScalars`, and `PresheafOfModules.sheafificationAdjunction`.
  The restriction node's Mathlib match supplies the ring-sheaf interface; its older
  fixed-coefficient recorded declaration is not a private replacement here.
- `Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor`:
  `siteDerivedConstantModuleFunctor` and its public
  `siteConstantModulePresheafGeneral` / `siteConstantModuleFunctorGeneral`;
  the equivalent commutative presentation is supplied in the dependency module.
- Mathlib `DerivedCategory`, `DerivedCategory.Q`, `HasDerivedCategory`,
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`; the existing upstream
  exact-functor module supplies `mapDerivedCategoryNatIso` and
  `mapDerivedCategoryCompIso`.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; Mathlib `Module.Flat` for the point-site terms.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: existing sheaf
  tensor and change-of-rings interfaces, used through their adjunction universal
  property rather than a second tensor product.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, publicly reexporting
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, the general
  ring-sheaf declaration also reexported by the recorded
  `Sheaf.Paper.EtaleDerivedScalarTensor` module. The latter's specialized etale
  declaration is not sufficient on an arbitrary site; the imported general
  interface gives the K-flat computation and normalized adjunction. The local
  helpers expose precisely its canonical adjunction and representative maps at
  independent localization sizes.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor`. Its already-landed node and the normalized
  derived coefficient adjunction node are added to `stmt_deps`.

Edge cases checked: the empty site and degenerate topologies (no terminal object
needed); zero rings and zero complexes; arbitrary non-flat ring maps; identity
maps; the zero target ring; unbounded complexes in both directions; distinct site
object and morphism universes and independent derived localization sizes. The
constant-section normalization extends uniquely by sheafification even where
constant sections alone are not all global sections. No finiteness is hidden in
any quantified term, coproduct, or resolution assumption.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "Derived constant sheaf realization commutes with
  unbounded derived extension of scalars and the scalar adjunction unit"`: eight
  ordinary constant/sheafification and adjunction hits, no derived comparison.
- `msearch.py ... loogle "CategoryTheory.constantCommuteCompose"`: three hits,
  namely constantCommuteCompose, its hom component formula and constantSheafAdj
  counit compatibility; these compare postcomposition, not derived scalar extension.
- `msearch.py ... grep "derived.*[Ss]calar|[Cc]onstant.*[Tt]ensor"
  CategoryTheory/Sites`: no hits.
- `rg` of `siteDerivedConstantModuleFunctor`, constant/derived/scalar comparison
  names in `WeilConjectures` and `lean/Sheaf`, and the exact item id in upstream:
  the recorded exact constant functor and related specialized comparisons exist;
  no declaration states this arbitrary-site S-linear comparison with both
  normalization clauses. Opened the actual recorded signatures and their
  docstrings, including the general scalar interface reexports.
- Read the cited local Stacks source at Tags 0G7E, 0D6D, 093J, 0GMW and 03CY;
  the K-flat computation, termwise sheafification and normalization match these
  sources. Q93's prior record is a stage-1 proof split/review, not a Lean delivery.

No statement correction or disputed statement. No new DAG notion is introduced.

## Dependency modules

`def-sfb-site-derived-constant-module-functor` receives a lean-only section 1(B)
repair in `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`.
The old declaration uses the constant RingCat sheaf; K-flat and sheaf tensor
interfaces use the underlying ring sheaf of a constant CommRingCat sheaf.
These are canonically isomorphic but not definitionally equal, so its target is
unusable verbatim with the recorded tensor interfaces. The module publicly retains
the original construction, then sheafifies the same constant module presheaf
using the forgotten commutative sheafification unit. Its named local-bijectivity
and exactness facts give exact localization. `realizationRingIso` is Mathlib's
`constantCommuteCompose`, and `commutativeSiteConstantModuleFunctor_transport`
states explicitly that coefficient transport recovers the old ordinary functor.
No definition data are sorry; all properties have full proof docstrings.
The dependency node's fields other than lean are unchanged.

## Validation

Both delivered modules compile through `scompile.py` with no errors or warnings
other than the expected postponed-proof warnings. The delivery compiles each file
separately in dependency order against the private side-project overlay.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
