## Worker report

Q13 stage 2, repair of immutable returned head 7d56b0c9ce0a. The delivery states
`AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing` in
`Sheaf.Paper.SmoothPurityTowerGluing`. The assembly docstring and single theorem `sorry` remain. All data definitions are complete.

The sandbox was compared with the live node and the returned report. The live
node still has no Lean record and its original eight statement dependencies;
its mathematical text and assembly proof agree with the returned delivery.
The repair starts from those current fields and applies only the stage-2 Lean,
statement-dependency and explicitly requested proof-dependency deltas. The
prescribed delivery tool builds the packet on current sheaf-dag.

Sources read: current blueprint `literature/blueprint/latest/blueprint/`;
`sec-smooth-purity/sk-prop-sp-tower-geometric/` gluing statement and proof;
the node itself; the new ownership nodes' existing declarations; and all of
`SmoothPurityTowerCoordinateAdjunction.Construction`, with its category,
tensor and right-comparison definition modules. Its live definition is now
available and pins precisely the composite previously approximated by the
rejected `CounitWord`.

Returned H2 is repaired as follows. The statement no longer cites
`lem-sp-tower-chart-admissibility` or `det-sp-tower-p1-adjunction` for plain
structures. New existing:true definition nodes own the actual `Twists` and
P1 `Presentation`, `Maps`, `AdjunctionData`, and their helper definitions.
The admissibility theorem remains a proof dependency. The P1 theorem and graph
summand theorem are used by the definitions and their owner records, but are not
assembly proof steps; the item proof_deps now exactly equals the union of the
seven proof-step `uses` entries required by review_split. The proposition
`Construction` is also a plain definition formerly recorded in a theorem node,
so a third existing:true definition node owns it. These ownership records reuse the existing declarations without aliases.

Returned H3 has two interface defects in GraphCoordinates, both repaired here.
The former unit_sections and counit_sections compared a bundled ModuleCat
morphism with an unbundled function. They now compare the eta-expanded
function `fun x ↦ component x` with `fun x ↦ x`; thus both terms have function
types and the identity-coordinate presentation can satisfy them.
The former push_sections also imposed equality of input and output section
carriers of the arbitrarily presented geometry push. It is removed.

Its replacement is GraphCoordinates.push_evaluation. For every f, graph module
M, coefficient level n and pro-etale V, it compares the eta-expanded function
of the graph-coordinate push component at (n,V) with the eta-expanded function
of `(o.geometry f).ordinaryPushEvaluation n` on presentation.inverse(M) at V.
This is an iso-level normalization: the right side is the GIVEN evaluation
isomorphism, not identity on the incoming section. The two functions have the
same source up to the ordinary presentation's coefficient transport. Their
outputs agree after the presentation unit/counit identifications. It permits
a carrier-relabelled push and excludes independently negating the push iso.
There is no new condition on the universally quantified o.

The accepted ConstructionAt and EtaleNormalized repairs are retained.
ConstructionAt is Construction with its chart existential and introductory
comment removed, and that same chart as an explicit parameter. All prefix
normalizations and suffix equations remain. Charts.etale_normalized constrains
the ACTUAL calculus used in ConstructionAt, not an independent witness. It
quantifies over every separated, locally finite-type, quasi-compact etale
k-map between the standing bases and every compactification. There is no
open-immersion, surjectivity or finite-map restriction, or restriction on the
objects of the original full ctf category.

Construction sketch for arbitrary valid o (including carrier relabellings):

1. Identify the coefficient sheaves B and tau with the graph model's constant
   graphRings and graphTransitions. Their quotient rings and adjacent maps
   agree. Change only the scalar presentation of each ordinary module sheaf;
   retain its underlying sections, restrictions and component maps. Applying
   the inverse coefficient identification gives the inverse functor. Both
   unit and counit are the identity functions on sections, satisfying the
   repaired eta-expanded pins. This construction does not involve o.
2. On each n and V, start with the actual ordinaryPushEvaluation component of
   o.geometry f on presentation.inverse(M). Its target is the canonical finite
   module direct image, whose sections are those of presentation.inverse(M)
   at the base-changed V. Transport these coefficients to the graph ring
   presentation and use presentation.counit to identify with M. These are
   invertible maps, natural in M and V and compatible with the adjacent quotient
   maps: they are the componentwise realization of the same ordinary strict
   system push, retained by Geometry's generic realization/transition fields.
   They assemble to the push isomorphism of ordinary systems. By construction
   its section functions are exactly the supplied ordinaryPushEvaluation,
   which is the new push_evaluation field. No identification of the incoming
   push carrier with the target carrier is asserted.
3. In particular, relabel a geometry push's carriers by an isomorphic copy and
   transport its evaluation iso, adjunction and other fields along that copy.
   The construction composes the relabelling with that evaluation iso. The new
   push_evaluation still holds. The old demand HEq(output,input) need not hold
   and is not used. All other graph transport helpers remain unchanged: the
   pull, open and sum squares are adjunction-unique, and their derived squares
   are the named canonical derived-composition maps. Thus arbitrary valid o
   has the needed coordinate data without adding a hypothesis to tower_gluing.

The predicate uses the published graph map `VaryingRingGraph.theta` on ordinary
unbounded derived strict systems. Its `theta_existsUnique` specification fixes
it on every homotopy representative: descend the graph-extension section map
degreewise, then apply the total right-derived direct-image unit. The section
map extends a lift summand by its own section on its clopen graph and by zero
on the complement. It is the canonical map FROM sum extension TO compact
support, so the equation in EtaleNormalized constrains `etale_shriek.inv`.
The exact existence/uniqueness characterization makes this existing definition
legitimate despite its theorem proof being postponed. No arbitrary existence
choice, arbitrary derived isomorphism, or faithfulness of level evaluations
is used in this repair.

The coordinate helpers make this a typed equation in the actual presentations:

- `graphRings` and `graphTransitions` are precisely the lifted positive quotient
  rings and adjacent quotient homomorphisms, used by the existing graph API.
- `GraphCoordinates.presentation` relates the two presentations of the same
  ringed sequence site. Its sections, restrictions and morphisms are fixed;
  both equivalence unit and counit are pinned as identity FUNCTIONS on sections.
  The direct-image comparison `push` is fixed by compatibility with the actual
  ordinaryPushEvaluation component, allowing its input carrier to vary with o.
  The helper supplies presentation data as a conclusion, not an extra theorem
  hypothesis or a restriction on input towers. The two ring systems agree
  by their definitions; the equivalence is their coefficient-transport identity.
- `graphPullCoordinates` is the left-adjoint-uniqueness comparison against this
  normalized push square. `graphOpenCoordinates` and `graphSumCoordinates`
  are then the unique ordinary adjunction-preserving left comparisons. Thus
  none can be independently negated. `graphForward` removes conjugation using
  the already normalized presentation unit.
- `graphDerivedSum` descends the actual ordinary sum comparison termwise.
  `graphSupportCoordinates` descends the open comparison and transports the
  proper image using the standard right-derived composition isomorphisms.
  The source equivalence preserves K-injectives, so this is genuine ordinary
  derived transport; there is no arbitrary map chosen by its finite levels.
- The defining equation of EtaleNormalized transports the actual
  `etale_shriek.inv` across these two words and equates it to the existing
  theta component. All coordinate factors are explicit named definitions.

The exact composite for clause 1 is now fixed at both stages. ConstructionAt
retains `_affine_hom` (actual P1 Hom map, open Hom map, root-normalized affine
comparison), `_step_normalized`, `_projection_successor`, `_iteration_zero`
and `_zero`. These pin ordered P1 integration, including d=0. Its final counit
equation composes inverse normalized right comparison, inverse compact-support
compositor, the etale-shriek comparison followed by the actual etale pair counit,
then the projection counit. EtaleNormalized now pins the previously missing
etale-shriek factor by graph extension. The ordinary adjunction-preserving
transport identifies the etale pair counit with fibre summation, without an
independent scalar. Charts.counit equates restriction of the global counit with
the SAME chart family's counit on `(c.precomp U.ι).copy he.symm`; the canonical
openComposition and actual openAdjunction counit remain unchanged.

Non-open sign-twist test requested by the return: take ell=3, E=Q_3,
k=an algebraic closure of F_5, and e:G_m -> G_m, z |-> z^2. This is a finite
etale double cover, separated and finite type, which is not an open immersion;
set d=0. Use its proper compactification and a constant coefficient tower.
After an etale cover splitting e, the source sum-extension stalk at n=0 is
F_3 direct-sum F_3 and the compact-support stalk is the same two sheets. The
graph map theta sends the first summand generator (1,0) to (1,0): this is
exactly its graph section/unit normalization, with zero on the other sheet.
Negating etale_shriek negates its inverse and hence the LEFT side of the new
normalization equation, which instead sends (1,0) to (2,0). The right side
is the fixed theta and still sends it to (1,0). They are unequal. Changing
LevelCompatibility.finite pairs or Levels.comparison cannot affect either
side of this equation: neither is referenced. Rechoosing GraphCoordinates
cannot hide the sign: its unit/counit section FUNCTIONS are identity and its
push square must agree with the fixed ordinaryPushEvaluation on every level
and section. Negating that square changes this function, so it fails the new
push_evaluation test on a nonzero generator. A carrier relabelling merely
transports both sides of that same test through the given evaluation iso;
it cannot absorb an independent sign. All remaining maps are derived by the
named adjunction/derived-functor operations. This is a test at a sheaf in degree zero,
so evaluating it at n=0 is a valid counterexample, without asserting that finite
evaluation detects arbitrary derived maps. On the zero object, or wherever
minus identity equals identity, there is no distinct negative comparison.
A simultaneous reparametrization of an etale sum adjunction is transported by
graphSumCoordinates and preserves the resulting fibre-sum counit; it cannot
produce the counterexample's independently negative local counit.

The repair uses the expressly allowed helper-predicate route. It does not
replace EtaleCalculus, change a dependency's recorded declaration, or modify
any citer. Thus no section 1(B) dependency replacement or citer audit is needed.
The node's mathematical statement is unchanged: this enforces its existing
canonical fibre-sum clause, not an extra mathematical hypothesis.

Hypotheses and all clauses, including the parts the maintainer checked correct:

- `(l : ℕ) [Fact l.Prime]`, `E`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` give the prime and finite coefficient
  extension. The actual ring `SpTowerShriek.R l E n` is O_E/ell^(n+1), so
  `n=0` is the first positive finite level, not the zero-exponent quotient.
- `pchar`, `_hp : 0 < pchar`, `_hne : pchar ≠ l`, `[Field k]` and
  `[CharP k pchar]` give the standing field and characteristic. Positivity
  and the field already force the characteristic to be prime.
- `X Y : Over (Spec (.of k))`, the separated, locally finite-type and
  quasi-compact structure maps, and `f : X ⟶ Y` give the standing k-schemes
  and k-morphism. `[SmoothOfRelativeDimension d f.left]`, `d : ℕ`, gives
  smoothness and pure relative dimension, including zero.
- `SpTowerCalculus.C` is the original FULL uniform constructible finite-Tor
  subcategory of ordinary strict derived towers. No normalization or
  restriction on its ambient morphisms is added. `b`, `o`, `q` are the
  existing section-normalized presentation data, not replacement operations.
- The actual compact-support functor is `SpTowerCalculus.F` for
  `CondensedRing.compactificationOverField f`. Preservation `hF` is concluded.
  `support` is only its full-subcategory restriction.
- The existential functor G and `adj : support ... ⊣ G` give the representing
  objects, the counit, and the prescribed bijection
  `a ↦ F.map a ≫ adj.counit.app K`, natural in M. They also give naturality
  in K, functoriality and both adjunction identities.
- Clause 1: for EVERY source open and etale coordinate chart satisfying the
  displayed factorization, `Charts.comparison` identifies the open inverse
  image of G(K) with the existing `originalChartRight` e* p_d* K(d)[2d].
  The ordered `affineTraceTower` is the existing presentation canonically
  isomorphic to standard affine d-space by `affineTraceAffineSpaceIso`.
  `open_properties` is concluded, so the ground-field structure of every open
  is retained. The explicit separated, locally finite-type, quasi-compact
  chart-map instances are consequences of this standing setting, not extra
  mathematical restrictions; the over equation in counit follows from he
  and the equation for f as a morphism in Over. No chart is excluded.
  The local Tate family is `Charts.twists`, fixed at ordinary finite sheaves
  and transitions. `Charts.etale_normalized` now pins the chosen calculus for
  ALL etale charts by the graph formula detailed above.
- Clause 2: `∀ K G' ε'` tests any competing pair satisfying exactly the given
  Hom bijections, then states `∃! i : G.obj K ≅ G'` with
  `F.map i.hom ≫ ε' = adj.counit.app K`. G and adj already supply the functor
  and right adjunction asserted by the node.
- Clause 3 is retained: `Levels.right`, `.adjunction`, `.realization` give
  the finite right adjoints on the entire finite ctf categories, with the
  existing ordinary-etale exceptional realization. `.comparison` is a
  natural isomorphism, `.support_evaluation` is pinned by Evaluation, and
  `.counit` and `.unit` are the two explicit compatibility equations.
- `coefficientMate` remains the genuine counit transpose of the inverse
  reductionDirectImageComparison followed by scalar extension of the finite
  counit, exactly as in det-sp-reduction-exceptional. `Levels.reduction`
  equates scalar extension of the level-n comparison, this coefficient mate,
  and right_m(r^K), with actual r^(GK) and the level-m comparison. All m≤n
  are quantified; the two invertibility fields are retained.

Definition dependencies used (full prefixes are AlgebraicGeometry.ProEtale):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: actual coefficient
  extension rings, through the existing tower definitions.
- Mathlib `SmoothOfRelativeDimension`, `CategoryTheory.Adjunction`,
  ObjectProperty full subcategories, their lifts and fully faithful inclusions.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spDerivedCoefficientEvaluation`, `spConstructibleTorTowers`, finite and
  tower full constructible categories.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.Base`,
  `.Operations`, `.R`, actual pull/push/tensor and compact-support operations.
- `Sheaf.Paper.CoefficientTowerShriekInterfaces`: `SpTowerCalculus.Coordinates`,
  `.C`, `.F`, `.realization`, `.Evaluation`, `.quotient`, `.reduction`,
  `.etalePullback`, `.etaleAdjunction`, `.openExtension`, `.openComposition`,
  `.FiniteCoordinates`, `.Preservation`, `.Calculus`.
- `Sheaf.SecSmoothPurity.ReductionExceptional`: the finite exceptional
  realization, scalar/support restrictions and the coefficient-mate formula.
- `Sheaf.Paper.SmoothPurityTowerChartAdmissibility`: `Twists` and its helpers,
  now owned by def-sp-chart-tate-tower-data; their finite Kummer data use
  def-sp-ell-twist-quotient-data and the intrinsic coefficient-twist definitions.
- `Sheaf.Paper.SmoothPurityTowerP1Adjunction`: Presentation, Maps,
  AdjunctionData and explicit epsilon/eta helpers, now owned by
  def-sp-tower-p1-adjunction-data.
- `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction`: the plain definition
  `SpCoordinateAdjunction.Construction`, now owned by
  def-sp-normalized-coordinate-construction. The theorem is not assumed.
- `Sheaf.Paper.SmoothPurityCoordinateCategories` and its already-landed
  definition node: `Bases`, `TwistFamily`, `ChartPair`, `originalChartRight`,
  `CompositeEquation`, `projectiveHom`, `openHom`, `etalePair`.
- `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` and
  `SmoothPurityCoordinateRightComparisons`: the existing pinned tensor,
  root, affine, zero and pullback comparisons used inside Construction.
- `Sheaf.AlgebraicGeometry.AffineTraceTower`: actual ordered affine spaces,
  projections and canonical coordinate identification.

- `Sheaf.Paper.VaryingRingGraphSummand`: sum, geometricSumAdjunction, graphMap,
  onHomotopy and theta, now with a definition owner. Its theta is fixed by the
  actual graph-on-summands construction and localization uniqueness.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`: Modules, ordinaryAdj,
  ordinaryOpenAdj, J and R, through def-sp-semilinear-constant-ring-operations.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp`:
  mapDerivedCategoryCompRightDerivedFunctorIso; the existing companion
  rightDerivedFunctorCompMapDerivedCategoryIso, rightDerivedFunctorNatIso and
  mapDerivedCategoryNatIso supply the actual normalized derived transports.

Edge cases rechecked: empty X and zero K have no Nonempty restriction; d=0
uses the explicitly normalized identity projection; e=id is allowed; n=0
means exponent one; reductions include m=n and the triple cases. The earlier
accepted full finite ctf quantifiers and genuine coefficient mate remain.
No equality of arbitrary derived maps is inferred from their finite levels.
Site object/morphism universes are unchanged. ConstructionAt uses the same
explicit universe u and the same types as Construction; no extra universe
equality is imposed.

Searches for the three retained ownership records were made before writing them:

- msearch LeanSearch, query “Strict Tate twist coefficient towers with normalized
  reduction maps and projective line adjunction presentation data”: eight
  unrelated perfection/scalar-tower/normalized-field-trace hits, no exact match.
- msearch Loogle `CategoryTheory.Adjunction, CategoryTheory.Iso`: twelve
  results, including ofNatIsoLeft/Right and their Hom/unit/counit formulas;
  this directly confirms the arbitrary-iso issue rather than solving it.
- msearch Mathlib grep `SpChartAdmissibility|SpTowerP1|Tate.*tower|tower.*Tate`:
  two unrelated scalar/Artin-Tate hits, no exact notion.
- rg of the exact declaration names in dag/nodes and project Lean found only
  the theorem-owned structures, the existing coordinate category/right/tensor
  helpers and the already-landed Construction. No definition node owned the
  three newly recorded interfaces. rg in WeilConjectures had no exact match.
- tools/blueprint_refs.py search tower adjunction found the geometric nodes;
  ancestor det-sp-tower-gluing identifies det-sp-tower-gluing as the source
  for these definition records.

Searches for the new graph ownership record, before creating it:

- msearch LeanSearch: “The graph map from etale sum extension to compact
  support is fixed on all homotopy representatives by extension by zero and
  the right derived unit”: eight unrelated compact-support function and
  homological-complex embedding hits; no graph map on strict systems.
- msearch LeanFinder: “Canonical graph extension from etale sum extension to
  compact support on strict coefficient systems normalized on homotopy
  representatives”: eight Homotopy.extend/ofExtend hits; no exact match.
- msearch Loogle `CategoryTheory.Adjunction.leftAdjointUniq`: twelve generic
  uniqueness and unit/counit formulas, used for coordinate transport. The
  first combined query also naming rightDerivedFunctorNatIso returned unknown
  identifier; its exact declaration was then read from the project source.
- msearch Mathlib grep `graphMap|etale.*sum|sum.*etale|theta_existsUnique`:
  ten unrelated simple-graph and etale-algebra hits; no matching graph map.
- rg in dag/nodes and project Lean found the actual graph map and theta in
  VaryingRingGraphSummand, recorded only under its theorem node. No definition
  node owns them. The existing semilinear-operation definition owner supplies
  the ambient operations. The existing ordinary-etale normalization node is
  a different finite-ring/site notion. WeilConjectures had no exact match.
- `tools/blueprint_refs.py search 'graph summand'`: zero blueprint nodes.
  The parent is the current det-sp-tower-gluing unit's Local pairs proof.
  All these search results are recorded in the new node's mathlib_searches.

Additional repair searches: rg for ordinaryPushEvaluation and GeometryBase
in lean/Sheaf and lean/WeilConjectures found the actual GeometryBase interface,
Geometry's normalized evaluation fields, and the specialized Geometry
ordinaryPushEvaluation/ordinaryPushEvaluation_eq in SmoothPurityTowerShriekLevels.
I read their signatures, field docstrings and ordinary unit normalization,
plus the concrete SemilinearProperOpen.push and the canonical module direct
image. No new notion, definition node or implementation is needed in this
repair; all four accepted existing:true owner records remain unchanged.

No statement correction or STATEMENT-DISPUTED finding. This repairs the Lean
rendering and definition ownership while preserving the mathematical node text.
Compilation and delivery checks are recorded below.

## New nodes

`def-sp-chart-tate-tower-data` is an existing:true owner for Twists and the
chart-domain, bound, and ordered-stage helpers already defined in
SmoothPurityTowerChartAdmissibility. It defines only the data and predicates,
not the admissibility theorem. Source: gluing Local pairs and Uniformity;
searches above and in mathlib_searches found no definition owner. The existing
finite quotient/Kummer-data node is cited rather than copied.

`def-sp-tower-p1-adjunction-data` is an existing:true owner for the P1
Presentation, Maps, AdjunctionData and all recorded helper definitions except
the existence theorem. Source: the projective-line unit/counit construction
used in Local pairs. The definition includes the normalized trace epsilon,
diagonal eta, finite evaluations and restricted-domain interfaces; it asserts
no existence. Searches above found the definitions but no definition owner.

`def-sp-normalized-coordinate-construction` is an existing:true owner for
Construction, the complete dependent existential specification from the
already-landed coordinate-adjunction module. It states no existence theorem
and retains every normalization equation. Source: gluing Local pairs and
Levels. Existing category, tensor and right-comparison definition nodes are
cited; searches found this exact plain definition only in its theorem record.

`def-sp-varying-ring-graph-comparison` is the new existing:true definition
owner of the sum/localization adjunction, graph section map, and theta uniquely
specified by its representative formula in VaryingRingGraphSummand. It imports
no copied implementation and asserts no new theorem. Its statement dependencies
reuse the already owned semilinear operations, etale/separated maps,
compactifications, adjunction mates and extension by zero. Source: Local pairs
and Stacks 0F4L, 0F4Y, 0GKM; searches above and in its record found no definition
owner of the existing construction. The theorem node supplies the defining graph construction used by the helper
record; the assembly proof dependency list contains exactly the proof-step uses. The three accepted ownership
records from the previous delivery are retained unchanged.

## Second reading by Q13

No second agent was started: the dispatch brief prohibits that and assigns
the independent reading to the maintainer. I checked the new equation with the
actual chosen calculus, not a second existential calculus. It mentions every
etale map in the standing setting, with no open-only condition, and constrains
the inverse comparison to the graph transformation whose section and homotopy
normalizations were read in full. The transports use only ordinary presentation
sections, the given push-evaluation isos, adjunction uniqueness and canonical
derived maps; there is no new free derived comparison. The non-open double-cover test above fails after a
minus-identity change. Levels is absent from this equation, so its free
finite adjunction choices cannot undo the failure. ConstructionAt's body is
unchanged from the accepted returned head. All accepted hypotheses, clause-2
uniqueness and clause-3 coefficient mates and reductions remain unchanged.

Validation: scompile.py compiled the repaired file in sandbox and actual module
views without errors or unexpected warnings (31.4 s and 29.8 s respectively).
The single named assembly theorem remains the only sorry. The accepted
ConstructionAt, EtaleNormalized, Levels, Charts, theorem signature and all four
owner records are unchanged; only GraphCoordinates' docstring and the three
returned normalization fields change in Lean. The prescribed deliver2.py
--no-push dry run passed server preflight and per-file compilation, producing
candidate 614adabfe75 with nothing pushed. It also validates that the
proof_deps list is exactly the union of the proof-step uses. Final delivery
repeats those checks with this validation record included.
