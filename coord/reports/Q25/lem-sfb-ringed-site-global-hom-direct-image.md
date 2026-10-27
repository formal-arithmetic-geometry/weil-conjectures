## Worker report

Stage 2, resumed Q25. The live node has the accepted six-step stage-1 split and
no Lean binding. No interrupted delivery was found. The previously interrupted
compile was polled before any new compile. This packet preserves the statement,
proof, sources, blueprint and reviewed stage-1 fields, and records a Lean statement
with one postponed theorem, `CategoryTheory.RingedSiteGlobalHomDirectImage.globalHomDirectImage`.
The missing scalar-valued sections definition and its generic global-Hom normalization
interface are supplied as two definition nodes. Neither asserts a new theorem.

The module quantifies over two small sites, two commutative ring sheaves, the
recorded ringed-topos morphism `f`, a commutative ring `A`, and the specified map
`t : A →+* Scalars B`. It uses the existing module categories and unbounded derived
categories, with the common module universe and a separately chosen derived-Hom
universe. There is no site-functor, final-object, flatness, boundedness or
quasi-coherence binder. The auxiliary presentations and all comparison structures
are conclusions of the theorem, not hypotheses on f.

`TensorData` retains the existing closed structures, representative models and
ringed tensor edge. `Presentation` stores the induced source scalar action, the
comparison of the edge's ordinary pushforward with f.modules, and the scalar-valued
sections identification. `PresentationValid` identifies the inverse image, direct
image, geometric adjunction and structural ring map with those of f (heterogeneous
equalities avoid expanding presentation types). It also gives the scalar-insertion
transpose equation for the module adjunction, the action on global scalars through
f.ringMap, and the normalized ordinary sections map through f.adj. These are
conclusions, and no site final object is required: only the terminal sheaf is used.

The derived comparison uses the canonical total right derived functor of the
ordinary module pushforward, via `rightIso`, with its shift compatibility. The
counit is normalized on complexes by the left-derived computation map and the
ordinary module counit. `leray` has direction G_D R -> G_C; its normalization is
the derived-unit equation after the ordinary sections identification.
`cup` is the actual tensor-of-counits adjunct using the existing uniquely normalized
ringed tensor comparison. `theta_formula` is precisely its evaluation transpose.
`comparison_formula` is inverse Leray followed by G_D(theta), in that order.
Both theta and the global comparison are natural transformations of bifunctors.

The all-degree conclusion is `cohomology_formula`, for every integer n and every
v : M -> N[n]. The right-hand side is R.map v followed by R.commShiftIso(n).
The two `HomIdentification` values are natural additive equivalences, pinned on
K-flat source representatives by the actual fixed K-injective resolution, the
actual internal-Hom localization factorization, and the product-projection
comparison with external cocycles. The cocycle morphism uses Mathlib's
Cocycle.equivHomShift inverse, Q's fixed shift comparison and the inverse of the
actual localized augmentation. Thus the equivalences are not arbitrary choices
that could make the cohomology equation hold tautologically. No isomorphism of
c or theta is claimed.

Dependency interfaces read and reused:

- `RingedToposMorphism` and `ringedSiteModules`: the specified geometry, module
  pushforward and sectionwise module category, not a second notion.
- `derivedInternalHomOfUniverses`: the recorded unbounded internal Hom, imported
  through the ordinary-module interface.
- `CoefficientClosedStructure`, `CoefficientTensorModels`: tensor-Hom adjunction
  with evaluation normalization and actual total K-flat representative models.
- `RingedTensorCorner`, `RingedTensorModel`, `RingedTensorEdge`, and
  `RingedTensorEdge.tensorComparison`: the existing canonical tensor comparison.
  `flatInclusion` simply restricts the existing K-flat natural comparison to
  representatives that also have flat terms; it proves no new tensor theorem.
- `coefficientHomResolution`, `coefficientHomResolutionIso`,
  `coefficientHomResolutionInverse`, `coefficientHomComponent`: actual fixed
  representatives and projections, rather than unlabelled existence isomorphisms.
- The existing `Functor.rightDerivedFunctor` and its computation unit, Q's shift
  comparison, homology factors and the ordinary HomComplex cocycle API.

I read the Stacks source for 0B6C (`remark-cup-product`), 0B6D
(`remark-projection-formula-for-internal-hom`), 0D6H (`lemma-Leray-unbounded`,
including its punctual-topos proof), and the recorded sections model for 08JA.
The scalar definition follows that punctual-topos interpretation with scalars
restricted along A -> Gamma(R). The current blueprint was searched in latest/;
this supporting general ringed-topos construction is not a separate blueprint
statement. The ancestor tool returns None for the inherited supporting node,
which is retained in the new node's from.node and explained here.

Edge cases read mathematically: the identity geometric morphism; the zero input
complex; the zero coefficient ring; an empty presenting site; singleton sites
with a nonflat ring map; and negative, zero and positive integer degrees.
Compatible families and the terminal sheaf work in the empty-site case. For a
nonflat ring map the pullback is derived and the cup need not be invertible;
no field asserts otherwise. All n range over integers and use the same fixed
shift convention, not a nonnegative Ext-only identification.

Searches for an existing statement (queries are from actual msearch logs):

- leanfinder: “A morphism of ringed topoi induces a canonical map on global derived
  Hom with cohomology action given by derived direct image”: ordinary pushforward,
  sections and global-element naturality hits; no unbounded comparison theorem.
- leanfinder: “The right derived direct image acts on global RHom complexes and
  sends every shifted derived morphism to its image under the derived functor”:
  exact-functor derived shift API and bounded rightDerived_map_eq; no match.
- loogle: `"DerivedCategory", "internalHom"`: no hits.
- grep in CategoryTheory: `globalHomDirectImage|global_hom_direct_image|RHom.*pushforward|pushforward.*RHom`:
  no hits.
- leansearch: “Natural comparison from derived global internal Hom to derived global
  internal Hom after direct image of ringed topoi”: ordinary sheaf pushforward,
  sheafHom and general localization comparison hits; no exact match.
- Project searches by the blueprint tag and globalHom/RHom/pushforward names in
  WeilConjectures and Sheaf found no exact project declaration for this item.

Additional logged API searches located the existing homotopy factor, shift class,
HomComplex cocycles, derived single/homology and Ext API; those are reused, not
claimed as new mathematics. The former two pending leanfinder sessions were polled
and their actual results read. The existing stage-1 mathlib_searches are unchanged.

## New nodes

`def-sfb-ringed-site-scalar-global-sections` defines compatible global families
as A-modules using a specified A -> Gamma(R), and their canonical total right
derivation. It is a missing independent definition, not a new theorem restating a
clause of this item. Its module contains real constructions and no sorry.
The source is Stacks 0D6H's punctual-ringed-topos interpretation of derived global
sections. Searches of DAG statements and the current blueprint, and searches of
WeilConjectures and Sheaf for scalar-valued global sections, found no such bundled
definition on arbitrary small ringed sites. Existing abelian global sections are
listed below. Mathlib searches, recorded verbatim in the new node, were:

- leansearch: “Global sections module of a presheaf of modules over the ring of
  compatible global sections”: SheafOfModules.sections, sectionsMk, Type-valued
  sectionsFunctor and scheme-specific module-action hits.
- leanfinder: “The global sections of a sheaf of modules form a module over global
  sections of the sheaf of rings”: ordinary sections, evaluation, unit and scheme
  module instances; no bundled functor with the prescribed external scalar action.
- loogle: `"PresheafOfModules", "sections"`: sections and their componentwise maps,
  which are reused, but no scalar-valued functor or its right derivation.
- grep in Algebra/Category/ModuleCat:
  `sections(Submodule|Module)|def sections|globalSections`: Type-valued compatible
  families and sectionsSubmodule for diagrams over a fixed ring. The new construction
  uses the same compatible families and restricts the varying ring actions along
  the evaluated scalar homomorphisms. A second phrasing was read before deciding
  there was no exact existing bundled definition.

`def-sfb-ringed-site-global-hom-identification` defines globalHom and the condition
HomIdentification: natural equivalences pinned by actual K-flat/K-injective cocycles.
It also names the transparent presentation of existing closed tensor data as a
RingedTensorCorner and restricts the existing natural K-flat comparison along the
flat-term inclusion. It asserts no existence and contains no sorry. Its source is
08JA and Equation 0A8Z, with 07A4/08J9 for the tensor representative notation.
It is separated from scalar sections because its input additionally includes the
fixed internal Hom and K-flat/K-injective representative interfaces. Existing
scheme, algebraic-space and pro-etale specializations are reused as conceptual
references but do not define this condition on arbitrary small ringed sites.
Mathlib searches used the exact logged queries:

- leansearch: “Normalized identification of global derived Hom cohomology with
  shifted derived morphisms using K-flat source and K-injective target Hom-complex
  cocycles”: Ext resolution and ordinary HomComplex cocycle hits; no such definition.
- leanfinder: “Morphisms from the free rank one module in the derived category to a
  shifted complex are its cohomology”: Ext and localized cocycle class API, reused.
- loogle: `"DerivedCategory", "internalHom"`: no hits.
- grep in Algebra/Homology: `globalHom|global.*[Hh]om|[Hh]om.*sections`: no hits.
- The blueprint search “global Hom” returned zero nodes. DAG and source searches
  found the existing general sections-model theorem and the affine-space normalized
  identification; their scopes and roles differ as below.

## Not duplicates

- def-sfb-ringed-site-scalar-global-sections vs def-sfb-coefficient-module-global-sections:
  the existing node forgets scalars to Ab; the new one retains an arbitrary specified
  A-action and takes the total right derived functor into D(A).
- def-sfb-ringed-site-scalar-global-sections vs def-pur-ringed-site-zeroth-hypercohomology:
  the latter records abelian H^0 after sections; the new definition retains the full
  scalar-valued derived complex.
- def-sfb-ringed-site-scalar-global-sections vs lem-sfb-ringed-site-unbounded-leray-sections:
  that theorem concerns evaluation at corresponding site objects for a continuous
  site functor and is Ab-valued; the new node is a definition on arbitrary small sites.
- def-sfb-ringed-site-scalar-global-sections vs lem-sfb-ringed-site-global-hom-direct-image:
  the item constructs a comparison under a ringed-topos morphism and identifies its
  all-degree action; the new definition has no morphism or comparison theorem.
- def-sfb-ringed-site-scalar-global-sections vs lem-sfb-finite-constant-unit-restriction:
  that theorem identifies a particular finite constant-unit restriction map; it does
  not define scalar global sections for general ringed sites.
- def-sfb-ringed-site-scalar-global-sections vs def-pur-proetale-global-section-maps:
  the latter defines pro-etale section maps for its fixed geometry; the new definition
  accepts arbitrary small ringed sites and an arbitrary global scalar homomorphism.
- def-sfb-ringed-site-scalar-global-sections vs lem-pur-proetale-direct-image-global-evaluation:
  that theorem normalizes a specific pro-etale direct-image evaluation; the new node
  defines scalar-valued global sections with no geometric morphism.

- def-sfb-ringed-site-global-hom-identification vs lem-sfb-derived-internal-hom-sections-model:
  the theorem asserts existence of Ab-valued representative isomorphisms and all-degree
  identifications; the new node defines the scalar-valued normalization condition
  using fixed representative maps and product projections, without asserting existence.
- def-sfb-ringed-site-global-hom-identification vs def-sfb-space-affine-global-hom-cohomology:
  the latter specializes to spaces over an affine scheme and their geometric compositors;
  the new node works on arbitrary small ringed sites with a specified global scalar map.
- def-sfb-ringed-site-global-hom-identification vs def-coef-ringed-tensor-hom-model:
  the existing node defines the tensor-Hom data; the new node uses those exact data,
  naming only their restricted corner presentation alongside scalar global Hom.

## Review by Q25

I checked the accepted six-step proof against the new statement rather than changing
its mathematics. Step 1 uses the module and derived adjunction statements and the
canonical tensor pullback characterization; TensorData, PresentationValid and counit_normalization
keep their actual maps. Step 2 uses the closed tensor-Hom evaluation and the tensor
comparison: cup and theta_formula spell out both arrows. Step 3 uses general
unbounded pushforward composition and the global-sections convention; sectionsIso
and leray_normalization express its unit characterization over A without a site
final object. Steps 4 and 5 use the K-injective Hom-complex sections model; the
representativeMap, Represents and cocycleMorphism definitions fix its projections
and its localized cocycle map, so the all-degree equivalences are not merely
unlabelled AddEquivs. Step 6 uses the same evaluation formula and derived counit/shift
compatibility; cohomology_formula contains precisely the resulting R(v) and shift
comparison. I verified that each cited statement supplies this input, including the
general-topos rather than site-functor scope of pushforward composition.

During elaboration I corrected the direction of Cocycle.equivHomShift, made the
coefficient universes explicit, replaced an expensive componentwise tensor adapter
by whiskering its existing natural isomorphism, and separated scalar-valued global
sections and the generic Hom normalization condition into independent definition
nodes above. The normalized geometry/sections equations are a proposition rather
than generated dependent record projections; their mathematics is unchanged. I also replaced an unnecessarily
unlabelled derived-functor unit package by identification with the actual library
rightDerivedFunctor and its shift-normalized computation unit. These are interface
and elaboration corrections; the accepted item statement and proof remain verbatim.

This is my own worker review. Direct delivery was explicitly requested; the maintainer
performs the independent review, and no second worker review is claimed.

I also checked the existing RingedDerivedComparisons.Lift interface against this
construction. It records general derived monoidal comparisons but no scalar-valued
global sections or global-Hom normalization; the existing tensor and adjunction
interfaces are used directly rather than copying its separate symmetric comparison
system.

The source-level profile showed repeated unfolding of the compatible-family sections
functor inside comparisons of termwise composites. The final interfaces keep that
real construction locally irreducible after its explicit component definitions;
unused generated injectivity/size machinery is disabled in the main interface.
No compilation limit was raised and no compiler or launcher was modified.
The stored additive and shift instances are used explicitly rather than registered
as globally inferable instances, because their presentation witness cannot be
inferred from the class target alone.


## Validation

All three modules compiled cleanly through the required scompile wrapper in
dependency order. The final run completed with exit 0; the main module compiled
in 50.3 seconds as the sandbox probe and 36.9 seconds as its library module,
within the unchanged 60-second limit. Only the item theorem is postponed; the two
definition modules contain no sorry. The item differs from the live node only in
lean and added statement dependencies, and its accepted statement/proof are unchanged.

The first delivery dry run passed compilation and requested the current empty
import_flags field on each new definition node. Both records were corrected; no
mathematical or Lean change was needed.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
