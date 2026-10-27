## Worker report

The item module `Sheaf.AlgebraicGeometry.SpacePicardSheafRepresentability` states
`AlgebraicGeometry.AlgebraicSpace.space_picard_sheaf_representability`, with `sorry`.
It follows the unchanged statement of the assigned node and Stacks quot.tex,
Situation 0D25 and Proposition 0D2C, and moduli.tex, Lemma 0DNI with the standing
hypotheses of section-picard-functor. These source passages were opened in full.
No statement correction or dependency-module repair was needed.

Clause-by-clause rendering:

* The base scheme is `{S : Scheme.{u}}`; the algebraic space is
  `{X : AlgebraicSpace S}`. The structural map is
  `f : X ⟶ groupSpaceBase S`, where the latter is the represented scheme S.
* Properness is `hproper : MapIsProper f`: the existing definition expands to
  separatedness, finite type, and universal closedness, exactly as in the node.
* Flatness is `hflat : MapIsFlat f`, the existing test on compatible etale scheme charts.
* Full finite presentation is `hfp : ProperQuotFinitePresentation f`: this expands
  to local finite presentation, quasi-compactness of f, and quasi-compactness of
  its relative diagonal. It is not replaced by local finite presentation alone.
* Every S-scheme is quantified by `T : ProperQuotTest (groupSpaceBase S)`.
  These are schemes over S with their (unique) map to the represented S. Thus
  these tests are equivalent to all objects of `Over S`, not just affine or
  etale tests, and no section of X/S is supplied.
* `properQuotFibre f T` is the actual sheaf fibre product X_T, with canonical
  projection `properQuotSnd f T`. `hO` requires
  `IsIso (moduleStructureMap (properQuotSnd f T))` for every such test.
  This is the canonical regular-function map O_T → (f_T)_* O_X_T, characterized
  on every scheme chart by the recorded module direct-image model. It is neither
  an arbitrary isomorphism nor the unit into an unidentified pullback module.
* The represented sheaf is specified by
  `Nonempty (SpacePicardPresentation f Q G)`. Its `lineClass` takes the actual
  small-etale modules satisfying the recorded `IsLineModule` predicate.
  `iso_class` factors through line-module isomorphism classes, and `naturality`
  uses the recorded `moduleTensorPullback (properQuotFibreMap f a)`.
* The presentation's `locally_represented` says every section is locally a line
  class on an fppf covering sieve. `locally_equal` is an iff saying equality
  of two line classes is exactly fppf-local isomorphism of their canonical
  pullbacks. These two conditions are the local surjectivity and local
  injectivity criterion for the associated sheaf. Since Q is already an fppf
  sheaf, they identify it with the sheafification of T ↦ Pic(X_T). This is an
  equivalent representative formulation, without choosing a large raw quotient
  and then asserting that it is definitionally a small-valued sheaf.
* `G : CommutativeSpaceGroup Q` is the existing natural commutative group
  structure on the functor of points. Natural multiplication, inverse and
  identity are actual algebraic-space maps since morphisms are natural
  transformations and fibre products are sheaf fibre products.
  `tensor_class` and `unit_class` pin these operations to the tensor product
  and trivial module. `inverse_class` pins a tensor-inverse line to group
  inversion; a rank-one module's canonical dual is such an inverse, so this
  states the dualization clause without introducing a second internal Hom.
* Quasi-separatedness is
  `MapIsQuasiCompact (pullback.diagonal (groupSpaceProjection Q).hom.hom)`.
  This is the relative diagonal over S, not an absolute diagonal over an
  unrelated scheme. Local finite presentation is
  `MapIsLocallyOfFinitePresentation (groupSpaceProjection Q)`, using etale charts.
* There are no assumptions on a section, geometric integrality, dimension,
  Noetherianness, connectedness, reducedness or the characteristic. The node's
  explanation of geometric fibres introduces no hypothesis and so adds no binder.

Dependency declarations read and reused:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom` and `Spec`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`,
  `structureSheaf`, `structurePresheaf_isSheaf`, `IsLineModule` and `EtaleSite`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`. This is the scheme counterpart mentioned in
  the node; space lines use `IsLineModule`, not Zariski modules on a space.
* `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`; its over-site
  is the existing `GrothendieckTopology.over S`, also used by AlgebraicSpace.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `moduleTensorPullback`, `moduleChartScalar`,
  `ModuleDirectImageModel` and `moduleTensorAdjunction`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`: `moduleStructureMap`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation` and their component definitions.
* `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotTest`,
  `properQuotFibre`, `properQuotSnd`, `properQuotFibreMap` and
  `ProperQuotFinitePresentation`.
* `Sheaf.AlgebraicGeometry.RegularGroupSpace`: `groupSpaceBase`,
  `groupSpaceProjection` and `CommutativeSpaceGroup`. No hypothesis from its
  separate `IsSmoothIntegralGroupSpace` predicate is used.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` and
  `TensorProductOfUniverses`: the existing `siteSheafTensorRight`.
* `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`:
  `SheafOfModules.CochainUniverseTransport.module` and `ring`, with the explicit
  site-object/site-morphism/coefficient/module/lift universes
  `u+1, u, u, u, u+1`. These lift section carriers and scalar rings by ULift.
  Tensor comparison with small lines is therefore fully faithful transport,
  not an additional equality between site and coefficient universes.

All recorded proof dependencies with usable Lean records are imported plainly:
SpaceCoherentStackGeneral, OpenStackAlgebraicLfp, Scheme, FinitePresentation,
Smooth, StackChartwiseSmoothEtaleCalculus, FlatInertiaAlgebraicSpaceQuotient,
SiteSheafificationSectionsLocal, AlgebraicSpaceFlatProperFpLocality and
AlgebraicSpaceFibreProductsEtaleCovers. AlgebraicSpace and Fpqc also occur through
public statement imports. Currently unstated proof dependencies are named in the
proof docstring: space-invertible-open-coherent, gerbe-smooth-universal-homeomorphism,
representable-fppf-etale-open-descent, space-module-isom-affine and
 gerbe-qc-diagonal-descent. They are not prerequisites for elaborating this statement.

Edge cases checked: for an empty base, the empty cover and the unique sheaf
sections are permitted. Over a nonempty base the empty family fails hO, as its
pushforward structure sheaf is zero; hO is not hollow. For the identity family,
hO holds and the associated relative Picard sheaf is trivial because lines are
locally trivial; locally_equal captures this rather than asserting global
isomorphism. Disconnected and nonreduced fibres remain allowed; no integrality
binder was inserted. Tests include non-affine and nonreduced schemes and all
characteristics. There is one freely quantified universe u and the module
transport uses its successor, not an independently smaller test universe.

Searches: msearch.py leanfinder queried the proper-flat algebraic-space Picard
representability statement (8 hits: scheme local representability and generic
module finite-presentation facts); loogle queried `"picardFunctor"` (0 hits);
grep queried `Picard|picardFunctor|relativePicard` (23 hits, ring Picard and
unrelated Picard-Lindelof). Leansearch queried representability without a
section (8 hits, ring relative Picard groups and proper scheme facts). The
additional new-notion Leansearch and LeanFinder queries and their returned
names are recorded in the new node's mathlib_searches. Direct rg of
lean/WeilConjectures, lean/Sheaf and dag/nodes found upstream scheme-only
Picard functors, the scheme-only FlatProperPicardAlgebraicSpace theorem and
generic ringed-site line quotients; none supplies this relative-space
representative presentation. `blueprint_refs.py search 'relative Picard sheaf'`
returned 0 matches, and its ancestor command returned None. Searches for this
item's id found no upstream declaration. No disputed statement was found.

Both delivered modules compiled cleanly through scompile.py, individually in
private dependency order: the new definition module took 7.7 s (2.6 s in its
sandbox check), and the item module took 3.4 s. Only named theorem proofs are
postponed: picardCommStructure_isSheaf (the defining sheaf-condition obligation)
and space_picard_sheaf_representability. All definition data are explicit.

## New nodes

`def-sfb-space-picard-presentation` defines the equivalent local-representative
presentation of the fppf relative Picard sheaf and its tensor group law. Its
source is quot.tex Situation 0D25, the sheafification local-section criterion,
and sites-modules.tex Tag 03EK. It owns SpacePicardPresentation and its helpers:
the commutative regular-functions sheaf, existing coefficient transport and
tensor, and canonical test refinements. The regular-functions sheaf's data
are exactly etaleForget.op followed by Scheme.Γ; only the named sheaf-condition
theorem is postponed. It does not duplicate the general ringed-site Picard
quotient in RingedSitePicardData, nor the scheme Picard functor in Picard.Defs.
The search queries, returned results, date and no-match verdict are in the
node. The item cites this node and the existing landed property, structure-map,
fibre-test and commutative-group nodes. Their records are unchanged.

## Second reading by NK

A separate final reading by this worker compared the unchanged item node, the
new definition node, and both final modules. Independent maintainer review is
still required by the delivery process; no second worker is claimed here.
The review checked each binder and conclusion against the clause table above.
In particular, full finite presentation contains both quasi-compactness clauses;
hO is the actual structure map after every scheme base change; all presentation
tests use the represented scheme S; and Q's diagonal is relative over S.
The tensor comparison initially exposed a size error, repaired using the
existing ULift transport with site hom universe u, rather than equating the
site-object universe u+1 with the coefficient universe u. The group-law
fields pin multiplication and the trivial class and therefore the dual inverse.
The presentation's local equality is an iff, and local representability ranges
over every section. These give both directions of the sheafification
identification. No hypothesis, conclusion, or source statement was changed.
