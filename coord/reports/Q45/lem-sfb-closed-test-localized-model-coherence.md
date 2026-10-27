## Worker report

The module Sheaf.Paper.ClosedTestLocalizedModelCoherence states
AlgebraicGeometry.ProEtale.ClosedTestLocalizedModelCoherence.closed_test_localized_model_coherence.
Its proof is sorry. The other declarations contain real constructions or explicit propositions
organizing this one statement. None selects an arbitrary map or an object from a mere existence
claim. No definition contains sorry. The theorem docstring records all eight proof steps.

Hypothesis and clause matching:

* The commutative condensed ring is Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1},
  with MonObj Λ and IsCommMonObj Λ. This is the underlying-object form of the recorded
  Profinite.CondensedRing. Modules Λ Y uses precisely Mod with condensedRingObj Λ Y,
  the underlying object of coefficientRing Y (Mon.mk Λ). No constant-ring substitute occurs.
* A : Type u, CommRing A, and 𝔞 : Ideal A give U = Spec A and the actual quotient
  closedMap A 𝔞. The existing closedSiteLift supplies the lift functor, inclusion and maps.
  V : (Spec (A ⧸ 𝔞)).AffineProEt retains the ind-etale basis condition; the two
  IsWContractibleRing hypotheses apply to Γ(V.left, ⊤) and Γ(v(V).left, ⊤).
* X, XZ, f, h, fZ and w : IsPullback h fZ f (closedMap A 𝔞) name the original
  cartesian square. IsAffine X and the explicit affine base give the affine morphism
  situation in the node. XZ may be any cartesian realization, so the isomorphism-of-square
  case is retained rather than forcing literal equality with the chosen pullback.
* K : DerivedCategory.Plus (Modules Λ X), I, I.IsKInjective and _e : Q.obj I ≅ K.obj
  express a K-injective representative of the specified bounded-below object. J.IsKInjective
  and j : h*I ⟶ J with QuasiIso j express precisely the second resolution. No K-injectivity
  of h*I, degreewise injectivity, monomorphic resolution, or boundedness of the chosen
  complexes is assumed.
* sourceTest and targetTest are the actual base changes in the full small pro-etale site.
  The site API orders these fibre products as B times_U X and V times_Z XZ. Their
  structure morphisms are the second projections. These are the canonical symmetries of
  T = X times_U B and T0 = XZ times_Z V = X times_U V; the normalized section comparisons
  therefore use the flipped IsPullback.of_hasPullback square, not an equality of different
  chosen limit objects. fibreTestArrow and closedFibreMap retain all projections and the
  specified closedSiteLiftInclusion. They construct the closed restriction a.
* sections is additive evaluation of the underlying internal module at that site object,
  termwise on cochain complexes. Thus Q.obj ((sections sourceTest).obj I) and
  Q.obj ((sections targetTest).obj J) are exactly C and D in D(Ab).
* unitAt evaluates the actual internal-module adjunction unit and restricts along the
  indicated site arrow. Its closed specialization closedUnit is the actual unit-section
  map; it uses the existing canonical adjunction rather than choosing a section. The
  recorded inverseSection is the section-ring version of that same operation; it is
  imported, not redefined. modelArrow is exactly Q of unitAt followed by evaluation of j.
* sourceUnit constructs the inverse direction of the source comparison: the actual
  closed unit, the derived evaluation unit, exact pullback factorization, and the
  K-injective direct-image comparison. targetUnit uses the literal direct-image section
  identity, the derived evaluation unit and Q(j) inverse. IsIso for these two maps supplies
  their inverses with exactly these normalizations. NormalizedComparisons additionally
  names these inverses eC and eD and pins them by eC.inv = sourceUnit and eD.inv = targetUnit.
  The equations there identify them with the existing geometric sectionComparison and
  closedComparison, including the target's transport by Q(j) inverse.
* localizationUnit is the ordinary unit at W followed by restriction to id_W, the
  universal sections unit and exact-pullback factorization. Under the induced slice-site
  identification, the ordinary part is the degreewise identity. The two IsIso clauses
  give the localized-section comparisons. evaluationLocalization is the existing
  closedFibreModuleDerivedRestriction at id_W, and eV in NormalizedComparisons is pinned
  to precisely this map. LocalizedModelEquation identifies the normalized r with the
  existing canonical localized restriction, transporting J back through j and coefficient
  pullback composition. No inverse of r or of the closed restriction is asserted.
* ResolutionCoherence quantifies over both replacement resolutions, a bounded-below
  replacement input K' and its identification Q(I') ≅ K'.obj, and every derived morphism α. Represents fixes the source and target derived arrows by Q(u) = α and
  Q(v) = Q(j) inverse, Q(h*u), Q(j'). Existence and uniqueness up to homotopy are explicit.
  The comparison homotopy j v ~ (h*u) j' is explicit as well. Its first equality is
  c ≫ r' = r ≫ d, i.e. d composed with r = r' composed with c in the node's convention.
  The next four equalities are the source, target, and both localized comparison squares.
  Invertible α gives invertible c,d, in particular for resolution changes representing
  the identity. The last clause sends homotopic representatives to identical D(Ab)
  arrows. Uniqueness of the homotopy classes supplies transition identity/composition laws.
* TestCoherence uses every a : V' ⟶ V with the two required w-contractibility hypotheses.
  sourceTestMap is base change of v.map a, and targetTestMap is base change of a.
  The first square uses literal presheaf restriction on the section complexes. The next
  two use rightDerivedFunctorNatTrans of the actual section restrictions. The final two
  equations are the localized comparison squares using sectionsArrow. ResolutionCoherence
  allows independent choices of resolutions at either test.
* GeometricCoherence gives the localization equations for the four sides f,s,h,fZ of
  this square and for its closed-test restriction. LocalizationAdjunction records both
  actual unit and counit equations, preservation of K-injectives by source restriction,
  and the K-injective computation of the direct-image comparison by ordinaryExchange.
  The latter is the underived adjunction mate of ordinary pullback composition; on slice
  sections its direct-image formula is the existing literal F(Y times_S W), and the
  displayed derived-unit equation fixes its derived normalization. The section-comparison
  cube uses all four cartesian faces and the actual exchange and pullComp maps.
  The restriction equation uses the same pullComp and equality of the two composites.
  WeaklyEtale base changes include every pro-etale base change and all isomorphisms.
  Quantification over cartesian realizations covers isomorphisms of the original square;
  on an affine localization, instantiate this theorem with its own quotient presentation
  and admissible local test. The two model equations and the cube then give the required
  normalized local model squares. A local lift is never equated to the base change of an
  old lift. Successive comparisons use the existing canonical composition normalization.
* All schemes live in u, small-site objects in u+1 with morphisms in u, and section groups
  in u+1, as in the published coefficient framework. No equality of site object and
  morphism universes is imposed, and no separate lower test universe is introduced.

Existing dependency declarations used, with their modules read:

* Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing,
  condensedRingObj, and its commutativity instance.
* Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod, Mod.forget and module morphisms.
* Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and its topology.
* Sheaf.Paper.CondensedModuleDerivedPushpull: CondensedRing.moduleObjectDerivedPushforward.
  Its ordinary functors, adjunction, exact inverse image and composition are the published
  ModuleObject.UpperLowerStar.Defs declarations.
* WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift: closedSiteLift.
  AffineClosedSiteFunctorProperties supplies its actual inclusion and cartesian square.
* WeilConjectures.RingTheory.ProEtale.WContractible: IsWContractibleRing.
* Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback and its projections;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
* Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions: the recorded general
  right-derived convention and its units. Here the concrete Grothendieck module categories
  already use the published rightDerivedFunctor, rightDerivedFunctorUnitQ and
  rightDerivedFunctorObjQIso; no arbitrary-quasi-isomorphism case is discarded.
* Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison: inverseSection.
* Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous: overFunctor, overMap and
  overFunctorMap, the sectionwise localized module interfaces. The internal-module form
  is computed directly by its existing unit and the induced site localization.
* Sheaf.Paper.ClosedTestDerivedExchangeModel: pull, adj, pullComp, square, exchange,
  sectionsOver, restriction, sectionsArrow, sectionComparison, and closedComparison.
  These real definitions have their own existing owner, def-sfb-closed-test-derived-exchange-maps;
  that already landed node is added to stmt_deps. No theorem from that module is copied.
* Sheaf.Paper.ProperWContractibleClosedFibreRigidity: closedFibreModuleEvaluation,
  closedFibreModuleSectionsRestriction, closedFibreModuleDerivedRestriction. Only these
  real helper constructions are reused; no properness or coefficient restrictions from
  that module's theorem enter this statement. The new definition owner def-sfb-closed-fibre-module-evaluation is added to
  stmt_deps in place of the theorem node. This tracks only the three constructions.

Proof imports include ClosedSiteAdjunction, SheafSliceDerivedComparison,
UnboundedSectionsLocalization, RingedToposDerivedPushforwardComposition,
ProEtaleWeaklyEtaleLocalization and Mathlib's KInjective Hom bijection and adjunction mates.
The two proof-only DAG lemmas lem-sfb-closed-test-unit-evaluation and
lem-sfb-closed-test-kinjective-section-models have no Lean records at the time of reading.
They introduce no undefined notion in this statement: the normalized maps are explicitly
constructed here using the published adjunctions and derived units. They remain named in
this theorem's proof plan; no missing-definition or resolution hypothesis replaces them.

Searches actually run:

* msearch.py leanfinder, "K-injective closed pro-etale test section resolution model
  naturality homotopy localization": eight hits, including InjectiveResolution.iso_hom_naturality_assoc,
  descCompHomotopy and isoRightDerivedToHomotopyCategoryObj_hom_naturality; these concern
  ordinary injective resolutions rather than the closed-test/K-injective/localization assertion.
* msearch.py loogle, `"rightDerivedFunctorObjQIso"`: zero hits.
* msearch.py grep, `Qh_map_bijective|isoRightDerivedObj.*naturality`, Algebra/Homology:
  ten hits, including DerivedCategory/KInjective.lean:41, the exact general Hom-bijection
  proof dependency already recorded by the DAG. No closed-test theorem.
* rg over lean/WeilConjectures and lean/Sheaf for closedTest, closed_test,
  localizedModel and localized_model; exact node-id search over WeilConjectures: no exact
  declaration. ClosedTestDerivedExchangeModel supplies the existing geometric maps and
  several geometric coherence theorems but not the independent-resolution model theorem.
  The generic evaluation and section restriction already occur in
  ProperWContractibleClosedFibreRigidity and are reused.
* DAG searches for ClosedTestDerivedExchangeModel and these helper names located the
  existing exchange definition-node owner and the theorem listing the proper-fibre helpers. blueprint_refs.py search
  "closed test section": zero blueprint nodes. The ownership repair below supplies the missing definition node for those helpers.

Source text read: derived.tex lemma-K-injective (070I), all three equivalent conditions
and proof; sites-cohomology.tex lemma-derived-pushforward-composition (0D6E) and
lemma-restrict-direct-image-open (0D6G), including the K-injective/ordinary section
normalization in their proofs. No source-based statement correction was required.

Edge cases checked: zero complex; identity derived morphism; two and three resolutions;
identity test and base-change maps; an isomorphism of cartesian realizations; ideal zero
(the closed immersion is the identity); unit ideal (the closed test is empty); zero ring;
empty affine schemes. There are no nonempty, nonzero, properness, finite-presentation,
torsion or geometric-invertibility assumptions. Pullback symmetries and target resolution
transport were corrected during compiler checking. All variables and universes are explicit.

Validation: scompile.py compiled the full module separately in sandbox and library modes
against the live published server build. Both succeeded without errors or warnings.

## Second reading by Q45

No second reading by a worker: the dispatched brief prohibits starting other agents.
The maintainer's independent review reads this delivery. The worker's final clause audit
is the detailed matching above; it is not presented as an independent review.

## New nodes

`def-sfb-closed-fibre-module-evaluation` records `existing: true` on
`Sheaf.Paper.ProperWContractibleClosedFibreRigidity` for precisely
`closedFibreModuleEvaluation`, `closedFibreModuleSectionsRestriction`, and
`closedFibreModuleDerivedRestriction`. Their full signatures and docstrings were read
at lines 60–99. Evaluation forgets the internal action and evaluates at the stated site
object; the section restriction is the actual adjunction unit followed by the pullback
site arrow induced by `(φ, id)`; its derived form uses `Functor.rightDerivedPullback`
and exact inverse image. Its source is Stacks 0D6F/0D6G, read in
`sites-cohomology.tex` at `lemma-unbounded-cohomology-of-open` and
`lemma-restrict-direct-image-open`. The derived unit characterization agrees with
`rightDerivedFunctorUnitQ_rightDerivedPullback_app` in the published upstream
`RightDerivedFunctor.ShortExactPullback` module. All coefficients, schemes, site objects,
module categories, morphisms and their projection equation are introduced in the node.
No theorem, properness or contractibility hypothesis is imported into its assertion.
The zero module, empty site object, terminal test, identity morphism and arbitrary
(non-closed) scheme morphism all remain admitted. Existing declarations are reused;
there is no new module or copied definition.

Fresh `msearch.py` LeanSearch and LeanFinder searches used the query
“Evaluation of internal modules on a small pro etale site and canonical derived restriction
of sections along a morphism of schemes”. Both returned eight hits, including
`SheafOfModules.evaluation` and ordinary module restrictions, whose categories differ
from the internal-module construction here. The Mathlib grep
`closedFibreModule|rightDerivedPullback` had zero hits. Repository `rg` in
`lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes` found the exact three declarations
only in the proper-rigidity module and its theorem's declaration list; no definition node
owned them. `blueprint_refs.py search 'closed fibre module evaluation'` returned zero
nodes; the ancestor command returns `None`, inherited unchanged from the item. The new
node copies that ancestry and puts this item at the front of its `via` list.

## Repair of return H2

The immutable returned head is `dc481024392d`. Its saved packet and the current main
node were inspected before editing. The initial prescribed dry run passed at
`ca4784804b5`, confirming that the recorded return was a semantic dependency-ownership
issue rather than a compiler failure. The packet now replaces
`lem-sfb-proper-wcontractible-closed-fibre-rigidity` in the added statement dependencies
with `def-sfb-closed-fibre-module-evaluation`, which owns exactly the three helper
constructions. The accepted `def-sfb-closed-test-derived-exchange-maps` dependency stays.
The Lean file, theorem signature, all mathematical clauses, and existing base node
fields outside `stmt_deps` and `lean` are unchanged. The advisory about explicitly
presenting isomorphisms of squares is optional; the accepted quantification over
cartesian realizations is retained. No statement correction is made.

Repair validation: the explicit `scompile.py` rerun passed in both sandbox (22.7 s)
and library (22.9 s) modes with no errors or unexpected warnings. Self-check confirms
the item differs from current main only in `lean` and `stmt_deps`, both recorded
signatures are verbatim, and the new definition node cites exactly its statement
dependencies. The first repaired dry run required the schema field `import_flags`;
an empty list was added, with no import defect flagged. This metadata addition
changes no construction or mathematical statement.
