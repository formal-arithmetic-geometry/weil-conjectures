## Worker report

Repaired `Sheaf.CategoryTheory.Sites.RepresentableSliceLocalizedRingedMorphism`,
with main statement `CategoryTheory.representable_slice_localized_ringed_morphism`.
The natural-language item is unchanged. All postponed statements belong to the
same node's comparison construction and have source and complete proof docstrings.
Definitions have actual data, or choose the unique object characterized by a named
theorem fixing its data. There are no unconstrained choices of isomorphisms.

Hypothesis-by-hypothesis correspondence:

- `C D : Type u`, `[SmallCategory C]`, `[SmallCategory D]`, `J`, and `K` present
  the two sites within a common arbitrary universe bound. Sheaves and modules use
  `Type u` and `SheafOfModules.{u}`. This retains the returned packet's size model.
- `[HasFiniteLimits C]`, `[HasFiniteLimits D]`, `[J.Subcanonical]`, and
  `[K.Subcanonical]` are the exact finite-limit and represented-sheaf assumptions.
- `U`, `[PreservesFiniteLimits U]`, and `[U.IsContinuous J K]` describe the given
  site functor. In the presence of finite-limit preservation, continuity expresses
  covering preservation. `U.sheafPullback (Type u) J K` with its continuous
  adjunction is the canonical chosen model of L. The main statement retains its
  explicit `PreservesFiniteLimits` hypothesis for L (advisory redundancy accepted).
- `R`, `S : Sheaf ... CommRingCat.{u}` are the given commutative coefficient rings.
  `a : R ⟶ U_* S` is the adjunct of c. The theorem's structural-map equation
  explicitly transposes the underlying map of a by the global set adjunction.
- `V : C` is the specified object, and `J.uliftYoneda.obj V` is h_V.
  `representableRingedSliceImageIso` is the recorded
  `Adjunction.uliftYonedaCompIso.app V`, hence precisely c_V, with no free choice.
- `sourceSlices` and `targetSlices` are the recorded slice data for R,h_V and
  S,Lh_V. The fibre normalizations explicitly use their `fibre_iso`, so arbitrary
  presentation choices cannot change the mathematical comparison.

Clause-by-clause correspondence:

- The two localized site charts are `representableRingedSliceChart`; their
  coefficient maps are sectionwise identities. Set and module chart restrictions
  are `representableRingedSliceSets` and `representableRingedSliceModules`.
  The first two conjuncts assert that the actual module restrictions are equivalences.
- The concrete slice map of sites is `representableSliceElementFunctor`: it sends
  `(W,b)` to `(UW,η_hV(b))`, with U on arrows. `representableSliceElementCoefficientMap`
  is a_W on each section. `representableSliceInverse`, `representableSliceRingMap`,
  `representableSliceStructuralMap`, and `representableSliceModulePullback` fix its
  inverse image, restricted coefficient adjunct, structural transpose and module
  inverse image before the comparison theorem is stated.
- `representableSliceRingedMorphism_unique` fixes EVERY data field of the slice
  `RingedToposMorphism`: inverse, direct, adjunction, ringMap, modules, and underlying
  module identification. The latter is identity, which eliminates automorphisms of
  the induced module identification. All other fields are propositions.
  `representableSliceRingedMorphism` chooses this unique structure. This is a
  uniquely characterized object, never a choice from bare existence or Nonempty.
- `representableSliceFibreComparison_unique` supplies a named theta between the
  concrete element inverse image on fibres and `Over.post L` followed by the target
  fibre functor. For every X,W,b,x its transposed map, followed by target fibre_iso
  and projection to the underlying section, is exactly η_X.left on the source
  fibre projection. This pins theta to `(H,φ) ↦ (LH,Lφ)` on objects and maps.
- The set map playing q inverse is `representableSliceSetPullbackMap`, the inverse
  mate of the EXPLICIT sectionwise identity `representableSliceSetPushforwardIso`.
  No final square chooses q. The main product equation additionally identifies it
  with theta on G×h_V, followed by `representableSliceProductComparison` and the
  target product fibre identification. That comparison's hom.left is exactly the
  Mathlib finite-product comparison, so both product coordinates are fixed.
  `representableSliceProductFibreIso` explicitly sends a fibre pair to its first
  coordinate and reconstructs it using the specified base element.
- The structural-map conjunct says that the fixed transpose of a_W equals this
  fixed restriction map at underlying R followed by restriction of c. Thus the
  slice structural ring map is restricted c, independently of any chart alpha.
- The chart direct-image set iso is uniquely sectionwise identity. Its inverse
  mate is `representableSliceSetChartPullbackMap` (alpha). The set restriction
  equation is precisely the equation from the returned packet with canonical
  alpha and q inverse replacing the free witnesses. It compares against the
  recorded `sliceSetPullbackMap`, including its units.
- `representableSliceModuleChartPushforward_unique` pins beta to sectionwise
  identity, including its restricted scalar action. The chart module map lambda
  is its inverse mate `representableSliceModuleChartPullbackMap`.
- The module direct-image restriction iso is explicitly sectionwise identity.
  `representableSliceModuleLocalizationSquare` transposes it vertically using
  the ACTUAL localization_modules adjunctions (transported along pullback_eq).
  `representableSliceModuleRestrictionMate` recovers that fixed square by the
  inverse vertical mate and takes its horizontal inverse mate. This is mu inverse.
  Thus mu is canonical before any final compatibility equation. It is the same
  inverse mate as `representableSliceModulePullbackMap`, by the equivalence laws.
- The four `IsIso` conjuncts assert invertibility of the canonical set restriction,
  set chart, module restriction and module chart maps. The last equality is the
  original module compatibility square using those fixed lambda and mu inverse,
  compared to the existing `sliceModulePullbackMap`. It cannot define mu.

## Repair of the returned H3 points

1. Replaced the free set comparison with a fixed inverse mate; the product
   normalization explicitly uses theta, both fibre_iso maps, and the canonical
   finite-product comparison. The restriction equation is now a test of fixed maps.
2. Constructed the unit-induced element-site map, the restricted coefficient map
   a_W and its structural transpose. A named uniquely characterized ringed
   morphism fixes all of its data fields. Its named theta has the global unit
   equation, which supplies the slice `(LH,Lφ)` formula. There is no existential sf
   whose ring map can be adjusted to solve the final ring equation.
3. Fixed beta by sectionwise identity and lambda by its mate. Fixed mu inverse
   by the sectionwise restriction square through the localization_modules
   adjunctions. The final square therefore has no free comparison witnesses.

## Dependency modules

`lem-weil-pbc-ringed-sheaf-slice-adjunction`:
`Sheaf.CategoryTheory.RingedSheafSliceAdjunction` retains the existing interface
and adds `pullback_eq : pullback = elementModulePullback R A` to the data.
A structure-field default is not a constraint, and its existing pullback_formula
only equates carriers; neither determined maps or scalar structures. The node
explicitly calls for the canonical sectionwise module restriction. The new equality
records that existing claim and allows localization_modules to be used on the
canonical functor. The existing existence construction supplies `rfl` for this equality. Its stage-2
proof is postponed, as required by preflight for a dependency module in this packet;
the full construction plan remains in its docstring. No source claim is changed.
All non-lean fields of the dependency node are unchanged.

Dependency declarations read and used (source modules are the recorded ones):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the presentation here uses its
  associated Grothendieck topology and Mathlib sheaves directly.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`:
  `CategoryTheory.siteInverseImage_tensor` and the canonical sheaf inverse image
  and adjunction used there. Its precoverage interface is not used to impose
  an extra covering-family closure assumption.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, with its specified induced module direct image.
- `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback`:
  `CategoryTheory.siteRepresentableAlgebraicPullback`,
  `siteRepresentableArrowMap`, and its upstream `Adjunction.uliftYonedaCompIso`.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`:
  `RingedSheafSliceAdjunctionData`, `ringed_sheaf_slice_adjunction`, and the
  re-exported `elementRing`, `elementSheafPullback`, `elementModulePullback`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`:
  `SheafOfModules.localizedRingedSiteMap`, `ringedSiteModuleMap`,
  `localize_ringed_site_morphism_general`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Mathlib.CategoryTheory.Sites.Over`:
  `SheafOfModules.overFunctor`, `GrothendieckTopology.over`, `Sheaf.over`,
  `GrothendieckTopology.overPullback`.
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`:
  `exists_localizedSheavesOverRepresentable_general`, `overPost_isContinuous`.
  The element-site fibre equivalences already supplied in the slice data give
  their represented specializations, via the explicit chart.
- Proof dependencies: `SheafOfModules.module_pullback_pushforward_adjunction`
  in `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`;
  `conjugateIsoEquiv`, `unit_conjugateEquiv_symm` in Mathlib Adjunction.Mates;
  `Sheaf.createsLimitsOfShape` in Mathlib Sites.Limits; and
  `sliceSetPullbackMap` / `sliceModulePullbackMap` in their recorded comparison
  modules. The size-convention node is metatheoretic and has no declaration.

Sources read: sites.tex `lemma-localize-morphism` (03CF), the representable
comparison (04D3), and sites-modules.tex `lemma-localize-morphism-ringed-sites`
(04J0), `lemma-localize-morphism-ringed-topoi` (04IF),
`lemma-localize-morphism-compare` (04J7). The two last structural-map formulas
are the same restriction of c, as encoded by the equation in the conclusion.

Edge cases checked: V need not be terminal or nonempty as a represented sheaf;
no points or global sections are chosen. Empty coverings and zero rings are
allowed. A nonflat or noninvertible structural map remains allowed: the theorem
asserts no exactness for the module pullbacks. Identity U and identity structural
map give the same restriction square. Infinite sites and modules remain allowed;
no finite-support hypothesis is imposed on sheaves or modules.

Searches actually run using msearch.py:

- LeanFinder, "localization ringed topos morphism at representable agrees with
  localized morphism of sites and module pullbacks": 8 hits, chiefly
  `PresheafOfModules.homEquivOfIsLocallyBijective` and scheme/topological
  localization maps; none is this statement.
- Loogle, `CategoryTheory.Over.post, CategoryTheory.GrothendieckTopology.overPullback`:
  0 hits.
- Mathlib grep, `representable.*[Ss]lice|[Ss]lice.*representable|localize.*[Cc]ompare`
  under CategoryTheory/Sites: 0 hits.
- LeanSearch, "localization morphism sites agrees slice geometric morphism
  representable sheaf": 8 hits, including sheaf representability and generic
  localization, none the ringed slice comparison.
- Mathlib grep for `representableRingedSlice|representable_slice_localized_ringed_morphism`:
  0 hits.
- rg of both lean/WeilConjectures and lean/Sheaf for represented-slice and
  slice-localized patterns: related comparison modules above, no exact match.
  grep of the item id in lean/WeilConjectures: no hits. The private slice formula
  in LocalizedSetPullbackComparison does not expose this ringed statement.


Additional searches during this repair (msearch.py, actually run):

- LeanFinder: "canonical morphism between categories of elements of representable
  sheaves induced by adjunction unit and module restriction mate": 8 results,
  primarily free presheaf-module/sheafification adjunctions and unitHomEquiv;
  none supplies the slice comparison in this node.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Over.post`: 0 hits.
- Mathlib grep in CategoryTheory/Sites:
  `representableSlice|slice.*[Mm]orphism|[Ee]lements.*adjunction`: 0 hits.
- Project rg for RingedToposMorphism, element/slice ringed morphisms and private
  continuous constructors found the existing continuous ringed-topos constructor,
  but its public theorem leaves geometric data unfixed. The repair instead fixes
  the unique full ringed structure with existing Mathlib site adjunctions.

No new independent node, statement correction, or disputed natural-language claim.
Every module is compiled separately by scompile.py against the live server build.

## Second reading by Q01

Author's second reading, since the dispatcher expressly forbids other agents.
I read the return's three numbered objections against the changed Lean and the
unchanged node. I checked that the structural map is now constructed before the
ring equation, beta is sectionwise identity, theta's unit equation actually uses
both fibre_iso projections, and the product equation contains the actual Mathlib
product comparison. The set and module compatibility equations now contain fixed
mates throughout, so they can no longer define free q or mu.

I checked the slice-module dependency with its structure open: its default did
not constrain the pullback field. The lean-only repair adds its functor equality
and lets the module restriction mate explicitly use localization_modules. Its
existing existence construction uses the identical functor; the stage-2 delivery
postpones its proof with the same full proof plan.
The source's zero-ring, empty-representable, identity-functor and nonflat-map cases
remain admitted. HEq appears only to compare literally specified maps across
proven equal presentations or equality of section carriers; it does not replace
any map specification. No hollow data definition is introduced: every choose uses
an existence-and-uniqueness theorem that specifies the maps, functors and units.
