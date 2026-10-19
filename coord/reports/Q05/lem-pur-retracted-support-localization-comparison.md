## Worker report

The module Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison states
AlgebraicGeometry.ProEtale.RetractedSupport.exists_comparison. Its only theorem proof
is sorry. All other declarations are transparent constructions or the structure
Comparison packaging the assertion. No new independent notion or dependency repair
is required: the auxiliary maps belong to this node and are listed in lean.declarations.
No statement correction is made.

The source read is main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1/
sk-prop-a1.proof.md: apply Rp_* to closed/open localization, collapse ps=id, retain
the connecting map, and then identify global sections with supported cohomology.
The node expands this argument to general bounded-below finite-coefficient inputs
and explicitly requires the local-class edge-map compatibility. Its twelve proof
steps are reproduced in the theorem docstring, including the cone sign calculation.

Hypothesis and object correspondence:

- The finite coefficient datum and A=A_{E,n} are P : PurityFiniteSetting, P.Ring
  and P.Coefficient. Modules P is ModuleCat.{u+1} P.Coefficient, with the prescribed
  standard ULift. finiteRing uses the existing positive-level finiteness theorem;
  finiteCoefficient is the ordinary ULift finiteness instance. These are actual
  existing constructions, not assumed new coefficient data.
- X,Y are Scheme.{u} with Over (Spec (.of P.field.k)). Each structure morphism has
  IsSeparated, LocallyOfFiniteType and QuasiCompact, exactly separated finite type.
- p : X ⟶ Y has IsOver over that same field and IsSeparated, LocallyOfFiniteType,
  QuasiCompact, exactly the separated finite-type k-morphism. No smoothness or
  properness of p is assumed.
- s : Y ⟶ X has IsClosedImmersion; hs : s ≫ p = 𝟙 Y is ps=id in Lean's composition
  order. Its being over k follows from p and hs; no independent hypothesis is added.
- j : U ⟶ X has IsOpenImmersion and QuasiCompact. hcompl is
  IsCompl (Set.range s.base) (Set.range j.base), expressing precisely complementary
  closed and open images. pi is the actual composite j ≫ p inside openTerm.
- EtSheaves and ProSheaves abbreviate the existing ordinary module sheaf categories
  on smallEtaleTopology and Scheme.ProEt.topology. nu/nuPlus are the recorded exact
  comparisonUpperStar functor's mapDerivedCategory/mapDerivedCategoryPlus.
- B ranges over every DerivedCategory.Plus (EtSheaves P X) in the fields of Comparison.
  input P X sends B to K=nu_X^* B in the unbounded coordinates, retaining its D+ domain.
  No boundedness above, constructibility or finite Tor-amplitude is assumed.
- closedTerm is input followed by sfFiniteExceptionalFixed P.Ring at
  Compactification.ofIsProper s, literally Y --id--> Y --s--> X. This is the
  prescribed finite transported exceptional inverse image. bounded_closed asserts
  existence of an integer lower bound for its cohomology, so C is in D+ as required.
- middleTerm is input followed by (lowerStar (Modules P) p).rightDerivedFunctor.
  openTerm is input, exact upperStar j, then rightDerivedFunctor of lowerStar (j ≫ p).
  hyper is right-derived global sections followed by homologyFunctor at q : ℤ;
  localClasses is homologyFunctor followed by global sections. These are modules,
  respectively cohomology sheaves, rather than unidentified underlying sets.

Conclusion correspondence (fields are qualified by RetractedSupport.Comparison):

- first and boundary are natural transformations in B. restriction is constructed
  from the derived open-unit and canonical direct-image compositor; it is not an
  existential arbitrary second arrow. distinguished asserts that Triangle.mk of
  these three maps is in distTriang for every B.
- etaleBoundary is a natural transformation on the ordinary etale derived category.
  etale_distinguished fixes its triangle with the actual closed counit and open unit.
  etClosed is the existing rightAdjoint of derived closed direct image.
- transportedTriangle applies derived Rp_et,* and then exact nu_Y^* using mapTriangle,
  including their shift comparisons. transport is an isomorphism of whole triangles,
  whose three components equal firstComparison, imageComparison and thirdComparison.
  Thus its third square includes the boundary and its sign. collapse uses the etale
  compositor, transport of hs, and the canonical derived identity isomorphism.
- firstComparison collapses Rp_* Rs_*, uses rightAdjointUniq with the specified
  identity/proper compactification and then the comparison unit. It therefore fixes
  the first arrow as the image of the actual counit. No pro-etale exceptional
  adjunction on arbitrary inputs is assumed.
- imageComparison uses comparisonDirectImageCanonicalMate and the standard D+/D
  coordinate isomorphisms. thirdComparison additionally uses
  sfDerivedComparisonPullbackIso and the etale compositor. These are precisely the
  canonical site comparisons, not arbitrarily chosen isomorphisms.
- supportIso is a natural isomorphism in B and every q : ℤ between H^q(Y,C) and the
  recorded supportHypercohomologyFunctor on K. It includes the requested q+1 degrees.
  complement identifies the chosen open j with the canonical openComplement object.
- middleGlobalIso and openGlobalIso use derived terminal evaluation of direct image,
  the K-injective composition comparison, and the recorded localization restriction.
  They implement H(Y,Rp_*K)=H(X,K) and H(Y,Rpi_*j^*K)=H(U,j^*K). They are actual
  constructions, not arbitrary isomorphisms supplied in the theorem.
- supportBoundary has the exact recorded SupportSequenceBoundary type, and
  support_exact asserts SupportSequenceExact. support_normalized fixes it on every
  bounded-below injective representative as the actual ShortComplex.ShortExact.δ
  snake boundary, using supportSequenceModelBoundary. This removes sign ambiguity.
- global_first identifies the first global map with the derived kernel inclusion.
  global_boundary identifies the third global connecting map, through supportIso,
  openGlobalIso and complementSectionsIso, with supportBoundary. It expresses the
  claimed H^q(Y,d)=partial, rather than just existence of unrelated connecting maps.
- edge is a natural transformation hyper → localClasses in every integer degree.
  edge_normalized/EdgeNormalization says that on every K-injective complex its map
  on cycles is the local cohomology class of that same section cocycle, using kernel
  comparison and homologyπ. This specifies the canonical edge map of the node.
- edge_boundary is equality of module morphisms: global boundary then e_C equals
  e_open then global sections of DerivedCategory.HomologySequence.δ of the original
  triangle. Equality of module morphisms gives the displayed formula for every alpha;
  openGlobalIso is the previously fixed identification of its domain with H^q(U,j^*K).
- etaleEdge and etale_edge_normalized specify the corresponding ordinary etale maps.
  etaleGlobalComparison is built from the comparison-adjunction unit and derived
  composition of etale sections with nu_*, and global_comparison_iso asserts its
  invertibility on all D+ inputs. etaleLocalComparison is the same sheaf unit followed
  by exact inverse image commuting with cohomology. edge_comparison states the
  commuting square for these actual maps. Their naturality, with transport's whole
  triangle isomorphism, identifies all triangle arrows and hence their global
  boundaries with the etale counterparts.

Dependency declarations read and used (including their full signatures/docstrings):

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting, Ring and
  Coefficient. The fixed positive level and finite field/extension are retained.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper, IsSeparated;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison: Scheme.proEtaleSiteComparisonModules
  is comparisonUpperStar ⊣ comparisonLowerStar in these exact fixed-module coordinates.
- Sheaf.Paper.SfDerivedDirectImage: sfFiniteDerivedDirectImage is the total finite-level
  direct image; here its fixed-coefficient lowerStar.rightDerivedFunctor component is
  used without the integral-reduction tower.
- Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage: sfFiniteExceptionalFixed
  is Rnu_* then etale rightDerivedUpperShriek then nu^*, at the specified compactification;
  sfDerivedComparisonPullbackIso supplies the canonical third-term pullback comparison.
- Mathlib.CategoryTheory.Triangulated.Pretriangulated: Pretriangulated, Triangle.mk,
  distTriang; Mathlib.Algebra.Homology.DerivedCategory.HomologySequence:
  DerivedCategory.homologyFunctor and HomologySequence.δ.
- Sheaf.AlgebraicGeometry.SupportCohomology: Sheaf.supportedSectionsFunctor and
  ProEtale.supportRestrictionArrow. Sheaf.AlgebraicGeometry.SupportLongExact:
  sectionHypercohomologyFunctor, supportHypercohomologyFunctor,
  supportHypercohomologyInclusion, SupportSequenceBoundary, SupportSequenceExact,
  supportSequenceModelBoundary. These are the dependency's existing kernels and
  derived sections; none is redefined.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: the ordinary module categories;
  Mathlib's DerivedCategory.Plus and IsGE give the all-integer lower-bound convention.
- Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle: exists_etale_closedSupportTriangle;
  Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison:
  comparisonDirectImageCanonicalMate. Their actual counit/unit and mate interfaces
  are used rather than treating their existence assertions as arbitrary maps.

The statement and proof dependency modules are imported explicitly except for
Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison: its published source imports
both the retired pro-etale Derived.LowerShriek and the newer FiniteCoefficient version,
which duplicate rightDerivedLowerShriekOfCompactification. As authorized by the brief
for duplicate imports, the smaller upstream Comparison.FullyFaithful module is imported
for the comparison-unit proof input. Its complete higher comparison assertion remains
a proof dependency in the DAG; no declaration is duplicated here. The old
Sheaf.Paper.FiniteDirectImageComposition similarly imports the retired
UpperLowerStar.Iso, conflicting with the newer FiniteCoefficient.Iso used by the
exceptional dependency. Its canonical universal compositor is supplied directly
by RightDerivedFunctor.Comp, which this module imports and uses. No import cycle
was identified. Helpers remain in the owning module and contain real data, so no new
DAG definition node or dependency module was needed.

Edge cases checked before completing the statement:

- Zero B and arbitrary integer shifts are admitted; q : ℤ includes negative and zero
  degrees. D+ carries only a lower cohomological bound.
- Empty Y forces empty X for a morphism p to Y, and empty U is permitted; there is no
  Nonempty assumption on any scheme or support/complement. The section s=id gives
  the empty complement and is admitted when p=id.
- General nonempty complements and arbitrary separated finite-type p are retained;
  neither p proper nor smooth is imposed. Positive coefficient levels are exactly
  P.level_pos and exclude only the n=0 case excluded by the source.
- The site remains the original small pro-etale site: Scheme.{u}, site object size u+1
  and morphism size u, with ModuleCat.{u+1} and the prescribed coefficient lift. No
  equality of site object/morphism universes or extra size hypothesis is imposed.
- Edge normalization uses the usual quotient from cycles to cohomology; it does not
  assume degeneration of a spectral sequence or surjectivity of an edge map.
- The global support boundary is fixed by injective-model snake normalization, so
  negating the triangle boundary cannot be accepted without changing those equations.

Searches for an existing statement (retained searches.jsonl and direct source searches):

- msearch leanfinder: “Closed section retraction localization triangle etale proetale
  direct image and global support boundary compatibility”. Eight hits, including
  Proj and etale-locus support lemmas; none is this statement.
- msearch loogle: “CategoryTheory.Triangle, DerivedCategory.homologyFunctor”. No hits;
  the remote index reported unknown CategoryTheory.Triangle. The actual local
  declaration sources and dependency interfaces were therefore read directly.
- msearch grep: “retracted.*support|support.*retract|hypercohomology.*edge”. No hits.
- rg of Mathlib, WeilConjectures and lean/Sheaf for RetractedSupport,
  retracted.*support, support.*retract and EdgeNormalization found only unrelated
  supported-perfect retractions and Cech edge normalization modules; no matching
  canonical localization comparison. The item id has no hit in upstream
  WeilConjectures. The DAG node and its dependencies were read directly.

Validation: the recovery dry run on 2026-10-17 returned
`OK (dry run): commit e2e7307123 passes the preflight and compiles; nothing pushed`.
The recorded theorem signature matches the source verbatim. Only the node's lean
field differs from the shared node; its date is the current UTC date. The module
has exactly one sorry, the theorem proof, and no line exceeds 100 characters.
No global build or direct git command was used.

## Second reading by Q05

This is the returning worker's self-check of the saved packet, not a claim of an
independent worker review; the dispatcher's maintainer supplies that independent
review. The full 647-line module, the current node and its sk-prop-a1 proof source
were opened. The saved mathematical work is retained without changes.

The theorem binders retain the finite datum P, both separated finite-type k-schemes,
the separated finite-type k-map p, the closed section s with hs, and the quasi-compact
open j with complementary images hcompl. Comparison quantifies over every bounded-below
B; closedTerm uses the recorded transported exceptional functor at the identity/proper
compactification. bounded_closed supplies exactly the promised lower bound.

The displayed triangle uses first, the constructed restriction, and boundary;
distinguished and transport identify the whole triangle with the etale triangle,
including its third square. firstComparison uses the actual counit-compatible adjoint
identification, collapse uses hs, and imageComparison/thirdComparison use the canonical
mate and pullback comparisons. Thus the transport is not an arbitrary identification.

For global sections, supportIso and global_boundary identify the third arrow with the
support boundary, normalized on injective models by support_normalized; global_first
fixes the supported-section inclusion. edge_boundary is precisely the all-integer
formula after the fixed openGlobalIso identification; edge_normalized takes the local
class of each global cocycle. The etale normalization and edge_comparison use the actual
comparison-unit maps. Zero objects, arbitrary shifts, empty schemes and the empty open
remain admitted. No new mismatch was found in this self-check; no statement correction,
dependency repair or new node was introduced.
