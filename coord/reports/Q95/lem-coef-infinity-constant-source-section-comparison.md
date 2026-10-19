## Worker report

The module `Sheaf.CategoryTheory.ConstantSourceSectionComparison` states
`SSet.Enhanced.constant_source_section_comparison`, with `sorry` as its entire proof.
Its auxiliary definitions construct the actual pullback and section complex. Its structures
specify this node's two comparisons, their normalization, coherent parameter dependence,
restriction squares, and cone compatibility. The repaired dependency `lem-coef-infinity-relative-hom-evaluation` has its own module
and one postponed theorem. There are no new independent definition nodes.

The natural-language statement and proof are unchanged. The retained packet already
contained the relative evaluation prerequisite, but its six unconstrained Prop fields did
not state that prerequisite. This repair replaces that interface and corrects the H8
documentation and H11 self-review deficiencies while keeping the item statement unchanged. Two already landed nodes, previously
proof dependencies, were added to `stmt_deps`: `lem-coef-infinity-pinch-comparison` supplies
the prism used in `first_formula`; `lem-coef-infinity-hom-bifunctor-functoriality` supplies
`canonicalHomComposition` for the cone formula. The latter uses the existing composition
package, rather than defining another composition on the right-pinched spaces.

Hypotheses and objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Universes U in U', independently sized | `u` and `max (u + 1) v`; there is no equality between `u` and `v`. |
| U-small simplicial indexing set J, arbitrary shape | `J : SSet.{u}`; `constantSourceBase J` is its degreewise universe lift. No category, Kan, filteredness, or nonemptiness hypothesis is imposed on J. |
| U'-small quasicategory E | `(E : SSet.{max (u + 1) v}) [Quasicategory E]`. |
| Locally U-small mapping spaces | `_hE : TransportLocallySmall.{u,v} E`, the dependency's existing predicate of equivalence to small Kan models. |
| Coherent transport and its given Hom bifunctor | Witnesses `T`, its `TransportClassificationClauses`, and `H : HomTransport E T` occur in the conclusion. They are supplied by the dependency theorem, rather than imposed as additional hypotheses. The same `H.bifunctor` is used everywhere. |
| Object x and coherent diagram p | Every comparison field quantifies `x : E _⦋0⦌` and `p : constantSourceBase J ⟶ E`. Bundling the comparisons for all J allows them to share the transport witnesses and point. |
| F(x,p) = H(x,p(-)) | `constantSourceHomRow H.bifunctor x p := p ≫ transportHomRow H.bifunctor x`. `constantSourceHomDiagram` constructs this simultaneously on `E.op ⊗ Fun(J,E)` by internal evaluation and currying. |
| Constant diagrams at x and at the point | `constantSourceVertex J E x := diagramVertex (SSet.const x)` and `diagramVertex (SSet.const star)`. The coherent left functor uses the dependency's `constantDiagrams`. The theorem requires `smallSpaceValue star.down = Δ[0]`, fixing the literal one-point space. |
| Source-fixed arrow fibration, ev0 fixed at x and ev1 variable | Existing `transportSourceArrows E x` and `transportSourceTarget E x`, whose definitions use the prescribed endpoint evaluations. |
| A(x,p) and its projection q | `constantSourceTotal x p := pullback p (transportSourceTarget E x)` and `constantSourceProjection x p := pullback.fst _ _`. These are constructed data. |
| Gamma's n-simplices are sections J × Delta[n] -> A over J | `constantSourceSections x p := transportOverHom (𝟙 J) (constantSourceProjection x p)`. Its underlying internal-Hom subtype imposes the map-over-J equation in every test degree and at every parameter operator. By Yoneda these are precisely the stated maps. |
| Left transformation space | `constantSourceMaps x p` is the existing right-pinched `mappingSpace` in the actual internal functor simplicial set `((ihom J).obj E)`, with the constant-source and p vertices. |
| Right transformation space | `constantSourceSpaceMaps H.bifunctor star x p` is the same mapping convention in `Fun(J,transportSpaces)`, from the constant point to the specified Hom row. |
| First and second equivalences | `ConstantSourceComparison.first` and `.second`, with `.first_equivalence` and `.second_equivalence`. Each has an inverse simplicial map and both simplicial homotopies. |
| All three displayed complexes are Kan | `ConstantSourceComparison.kan`. The empty complex is permitted by the dependency's positive-dimensional Kan convention. |
| A transformation is its arrow-valued section, on every higher simplex | `first_formula`: after evaluation into A's arrow coordinate, the image of an arbitrary simplex s is exactly `s` precomposed with the right-pinch prism. `constantSourcePrism` carries the J coordinate unchanged and puts the interval and simplex coordinates in their prescribed order. This includes the vertex formula for b and does not replace a simplex by its vertices. |
| Coherent contravariance in x and covariance in p | The coherent source and target functors are explicitly `constantSourceLeftFunctor diagramHom` and `constantSourceRightFunctor H.bifunctor star spaceDiagramHom`. `coherent` is one equivalence edge in `Fun(E.op × Fun(J,E), transportSpaces)`, with those exact endpoints. `components` identifies its maps, through the two normalized Hom comparisons, with `first ≫ second` on entire mapping spaces. The section family uses the same coherent structure transported through its prism-normalized first equivalence. |
| Compatible with restriction along I -> J | For every small I,J and every simplicial map v, `ConstantSourceRestriction` supplies the actual induced maps on the left and right transformation spaces, specified by `HEq` to `mappingSpaceMap` of internal precomposition. The section map is uniquely fixed by `sections_formula` after arrow evaluation, in all degrees. `first_square` and `second_square` are homotopies of entire-space maps. The additional `square` is a coherent square on the whole `E.op × Fun(J,E)` parameter base, with top and bottom equal to the J and I coherent comparisons; its vertical components are normalized to those same restriction maps. |
| Cone lambda: constant l -> p | `lam : (constantSourceMaps l p) _⦋0⦌` is precisely such an edge in `Fun(J,E)`. |
| Postcomposition f -> lambda composed with constant f | In `ConstantSourceConeFormula`, `k` is fixed by `mappingSpaceMap (constantDiagrams J E) x l`, and the left map then uses the existing `canonicalHomComposition` with lam. |
| On the right this is the coherent family (lambda_j composed with f) on the entire Map_E(x,l) | `mu` is fixed by applying `mappingSpaceMap (constantSourceHomAt H.bifunctor x)` to the whole lam, including J × Delta[1]. The right map inserts f into the Hom value, takes its constant diagram via `kS`, then postcomposes with mu in `Fun(J,transportSpaces)`. The homotopy compares maps with domain `mappingSpace E x l`, not just their vertices or components. |
| The right-hand constant family really is f, under the given H | `ConstantSourcePointInsertion` fixes its insertion in every enriched simplex: the initial block and final singleton are identities; a path to the final vertex uses the maxima-of-subsets formula and the actual map `H.pinch ≫ H.arrowComparison`. The constant-family homotopy in `ConstantSourceConeFormula` identifies `k ≫ first ≫ second` with this normalized insertion followed by `kS`. Thus the cone formula cannot be satisfied just by defining its right input to be the left composite. |
| A may be U'-small; Gamma has a U-small Kan model | A and Gamma are in `SSet.{max (u + 1) v}`. `small_model` uses existing `IsEssentiallySmallSpace.{u,...}`: a `SSet.{u}` Kan model and a weak equivalence from its ambient lift. No small-total-space assertion or extra smallness assumption is made. |
| Empty J and empty mapping spaces allowed | No nonemptiness binder occurs anywhere. Neither comparison map requires a chosen vertex in an arbitrary mapping space. |

The `HEq` clauses compare the specified canonical maps with their typed versions after equal
endpoints are identified. They do not quantify an arbitrary map without normalization. These
identifications account for the two equal presentations of a constant diagram and for its
restriction. All universes and variables are explicitly bound; `autoImplicit` is disabled.
The point-insertion declaration uses the enrichment that `transportSpaces` already carries
through its dependency; neither module changes any instance or attribute, and no alternate
space category is introduced. (Corrected by the maintainer's reviewer: an earlier sentence here
claimed a scoped `Spaces.kanEnrichment` attribute that the delivered module does not contain.)

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `diagramVertex`, `evaluation`,
  `constantDiagrams`, `mappingSpace`, `mappingSpaceMap`, `IsEquivalenceEdge` and the
  full recorded cone construction. These supply the literal coherent simplicial models.
- `Sheaf.CategoryTheory.SpaceTransportClassification`: `transportOverHomSubcomplex`,
  `transportOverHom`, `transportSourceArrows`, `transportSourceTarget`, `transportHomRow`,
  `transportHomValue`, `transportSmallEdgeMap`, `smallSpaceValue`, `transportSpaces`,
  `TransportClassifier`, `TransportClassificationClauses`, `HomTransport`, and
  `TransportLocallySmall`. The recorded theorem supplies the transport witnesses.
- `Sheaf.CategoryTheory.RightPinchComparison`: `rightPinchPrism` and the recorded
  `right_pinch_comparison`, including its full prism normalization and naturality.
- `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`: `canonicalHomComposition`,
  whose definition uses the existing mapping-composition theorem. This module is public
  because that declaration occurs in the cone predicate.
- The available proof dependencies `EnhancedFunctorConeCalculus` and
  `InfinityMappingComposition` are imported for their recorded theorems. The new
  dependency `lem-coef-infinity-relative-hom-evaluation` is stated in the companion
  module `Sheaf.CategoryTheory.RelativeHomEvaluation` and imported publicly. Its
  `RelativeHomEvaluationData` records the actual map over the parameter base, the
  all-simplex arrow formula, coherent naturality in both variables, parameter pullback,
  and the parameterized postcomposition square. The main theorem uses
  `relative_hom_evaluation` in proof steps 5 and 7; the dependency is present in
  `stmt_deps` and has its own node copy. No dependency wait or cycle is introduced.
- Mathlib's internal-Hom quasicategory instance from
  `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct` is imported
  publicly for the composition expressions in the cone predicate.

## Dependency modules

The prerequisite `lem-coef-infinity-relative-hom-evaluation` is an existing DAG node
without a usable landed declaration. The saved packet contained only an unusable stub
with six unconstrained Prop fields. I repaired its node copy
`dag/nodes/sec-six-functors/lem-coef-infinity-relative-hom-evaluation.json` and module
`Sheaf.CategoryTheory.RelativeHomEvaluation`. The module defines the parameter family,
pullback total space and projection, the coherent source and target diagrams,
`RelativeHomSquare`, `RelativeHomEvaluationData`, and `RelativeHomPullback`; its
only postponed theorem is `relative_hom_evaluation`. The companion node retains the exact
source statement and records the module signature.

Edge checks: for empty J, the actual maps-over-J section complex has one section in every
degree, so the two equivalences give the required point. For J = Delta[0], the formulas
reduce to the arrow/mapping-space comparison and the point-to-Hom insertion. A missing arrow
at a vertex makes the section complex empty, and all inverse-map and Kan assertions still
make sense. For a fixed cone, its domain mapping space can be empty; the formula asserts
equality up to homotopy of maps from that entire empty complex without requiring an element.
The n = 0 prism is the original arrow; higher n retain the whole parameter simplex. Arbitrary
indexing sets are lifted to the ambient universe, without changing their size condition.

Searches performed before writing:

- `msearch.py` LeanFinder: “Mapping spaces from constant diagrams in quasicategories are
  section spaces of the source fixed arrow left fibration”: eight hits, including
  `SSet.const`, `SSet.const_app`, nerve edge and truncated homotopy-category declarations;
  none supplies the comparison or its parameter coherence.
- `msearch.py` LeanSearch: “The mapping space from a constant coherent diagram is the
  section space of its mapping space left fibration”: ordinary-category results
  `Functor.sectionsEquivHom`, `Limits.compCoyonedaSectionsEquiv`, `Sheaf.ΓObjEquivHom`,
  and set-valued sections. Their returned signatures concern sets of transformations,
  not coherent transformation simplicial sets.
- `msearch.py` Loogle: `"mappingSpace", "section"`: zero hits.
- `msearch.py` grep: `section|constant|mapping` under `AlgebraicTopology/Quasicategory`:
  eight hits, consisting of section headers and ordinary quasicategory primitives;
  no section-space comparison.
- `rg` on the source project's `WeilConjectures` and side `lean/Sheaf/CategoryTheory`
  for constant-source and section-space names, and `grep -rn` for this exact node id:
  no existing declaration. Existing relative-cone tests and transport constructions
  found in the side library address other statements and are not replacements.
- Exact proposed names were checked against `dag/lean_names_upstream.json`, source
  `WeilConjectures`, and side `lean/Sheaf`; no collision was found.
- Mathlib's simplicial homotopy file and `KanMappingHomotopyInvariance` were checked for
  an existing named predicate of two-sided simplicial homotopy equivalence. The comparison
  predicate simply records the two inverse homotopies required here.

Sources opened: [Kerodon 03MR](https://kerodon.net/tag/03MR),
[05QM](https://kerodon.net/tag/05QM), and [01L5](https://kerodon.net/tag/01L5).
They are the Hom-transport, section, and pinch sources identified by the node; the complete
parameter-natural statement is explicitly agent-formulated in its source record.

No statement correction or disputed statement is needed. The two `sorry` declarations are
`constant_source_section_comparison` and `relative_hom_evaluation`, each matching its DAG
node. Their docstrings contain respectively all eight and all seven proof steps. Every
helper definition has real data.


## Second reading by Q95

This is the author self-check requested by the dispatcher; the maintainer supplies the
independent review. I read both node statements and both complete modules again. The
saved packet's dry run passed at `cc50ca8a10`, but it still had the six bare `Prop` fields
from returned head `20e8843180a7`; a clean compile did not fix those semantic defects.
I retained the main module and repaired the companion dependency instead of re-pushing it.
The current dependency copy was refreshed from the shared DAG; its seven proof steps and
stage-1 review are retained unchanged. Only its `lean` record is delivered.

H3/H13 corrections, checked against every clause of the dependency statement:

| Natural-language hypothesis or clause | Exact rendering and finding |
| --- | --- |
| Fixed small universe W and containing universe | Native `B C E K : SSet.{w}`; categories of small spaces and left fibrations live in `w + 1`. `relativeHomLiftFamily` retains both input coordinates. `relativeHomEnlarge.{w,v}` is the actual `uliftFunctor.{v}.map` of any full transformation, classifier, Phi or comparison square; no new witness is chosen on enlargement. |
| B,C,E are quasicategories; K is any small simplicial set | Explicit `[Quasicategory B] [Quasicategory C] [Quasicategory E]`. K is quantified in the conclusion with no category, Kan, or inhabitance assumption. |
| i, t, and T are simplicial maps | The main binders `i : B ⟶ C`, `t : B ⟶ E`, and the conclusion's `T : K ⊗ C ⟶ E`. |
| Entire restriction to K times B equals t after projection | `hrestr : (𝟙 K ⊗ₘ i) ≫ T = snd K B ≫ t`; this is equality of natural transformations, not a check on vertices. |
| M and the actual pullback source-fixed arrow fibration | `mappingSpace C (i.app _ b) c`, `relativeHomFamilyAt T c`, `relativeHomEvaluationTotal t T b c`, and `relativeHomEvaluationProjection t T b c`. The last two use the existing `transportSourceTarget E (t.app _ b)`. |
| Phi over K with its displayed all-simplex formula | `phi` has domain `K ⊗ arrowMappingSpace C (i.app _ b) c`; `phi_over` fixes projection to K. The former `phi_formula : Prop` is replaced by a universally quantified equality for `n,m,a,k,h,s`. After both pullback arrow projections its value is `T.app m (K.map a k, h_at_m_a_s)`. This fixes the entire internal arrow, hence Phi, without choosing an arbitrary map. |
| Right-pinch j rather than a freely chosen comparison | `pinch`, `pinch_formula`, `pinch_weak`: the equality after `arrowMappingSpaceInclusion` is the prescribed `rightPinchPrism` formula on every simplex. The inclusion is monic, so this fixes the canonical j. |
| Given coherent Hom bifunctors of C and E | `HC` and `HE` are the existing `HomTransport` on the degreewise lifted native categories and the same `Tr`. All `TransportClassificationClauses (Tr A left)` occur in the conclusion. No alternative Hom structure or added Hom-functor hypothesis is used. |
| Actual coherent epsilon with both specified endpoints | `epsilon` is a map `(B_up.op ⊗ C_up) ⊗ Δ[1]` into the internal functor set from K_up to `transportSpaces.{w,w+1}`. `epsilon_source` and `epsilon_target` identify its restrictions with the explicitly defined `relativeHomSource` and `relativeHomTarget`. The former is constant on K; the latter evaluates `HE.bifunctor(t(b),T(k,c))`. The former unconstrained `epsilon : Prop` is gone. |
| Mapping comparison sends epsilon to Phi composed with id times j, coherently in b,c | `sourceFamily` and `targetFamily` are full coherent diagrams in the existing enriched nerve of native small left fibrations. `source_objects` fixes the product K times M and its projection; `target_objects` fixes the actual A and q. `arrow` has those endpoints. `arrow_formula` identifies its components via the existing, maximum-path-normalized `TransportNerveComparison` with the map `((𝟙 K ⊗ₘ pinch b c) ≫ phi b c)` on the entire source space. The native classifier is an actual simplicial map with `IsFunctorEquivalence` and `IsFullyFaithful`. `sourceComparison` and `targetComparison` are coherent equivalence edges with four fixed endpoints. `transport_square` has exactly `arrow`, `epsilon ≫ classifier`, and these two comparisons as its four boundaries. Thus the transport identification is a square in the full coherent functor category, rather than an unrelated proposition or a statement on component sets. |
| Postcomposition square, including K times Delta[1] and higher composable families | `naturality` quantifies over any `P : SSet.{w+1}` and any `a : P ⊗ Δ[1] ⟶ B_up.op ⊗ C_up`, and supplies `RelativeHomSquare`. Its top and bottom are the two pulled-back epsilon transformations; its sides are `a ≫ relativeHomSource ...` and `a ≫ relativeHomTarget ...`. Specializing a to constant b and a C-edge gives the stated postcomposition square. Both sides use the existing HomTransport actions, so they are respectively constant postcomposition and HE applied to the whole T(-,u). The transport square restricts along the same a, retaining its higher simplices. |
| Analogous precomposition square | The same `naturality` field with a in B_up.op and constant c gives precomposition by i(v) and by t(v); `hrestr` fixes the latter over every K-simplex. This replaces the bare `precomposition : Prop`, without treating each vertex of B independently. |
| Arbitrary simplicial parameters and parameter-base pullback | The same P quantifier permits arbitrary additional simplicial parameters. The theorem chooses D simultaneously for all K,T,hrestr with shared HC,HE. For every K',r it gives `RelativeHomPullback`: a square of entire epsilon maps relative to their fixed endpoints, an actual `IsPullback` square of total spaces, unchanged arrow coordinates, `phi_eq`, and `pinch_eq`. It also retains the existing enriched `TransportPullback`, naturality of the classifier under that pullback, the square on the entire arrow transformation, and a cube connecting the two specified transport comparison squares with that arrow square as its boundary. Thus it compares the chosen transport identifications themselves. This replaces the bare `parameter_pullback : Prop`. |
| Compatible enlargement of containing universe | The construction stays in the least containing universe and `relativeHomEnlarge` maps every actual map by the degreewise ULift functor to any larger universe v. Thus all boundary equations, Phi formulas, and the whole transport square are lifted together. This replaces the former free `universe_change : Prop` by a real construction. |
| No equivalence assertion for epsilon or sections | Only the classifier and the changes of representative are equivalences. There is no `IsEquivalenceEdge epsilon`, no section-space assertion, and no inverse of Phi. |
| Empty K and empty mapping spaces | No `Nonempty K`, chosen K-point, or chosen mapping-space vertex occurs. The product source and actual target total spaces are empty when K is empty. All maps and squares still type, and the naturality assertion uses only maps from the possibly empty source. |

H8 documentation correction: every declaration in the dependency now names its source
place and the exact blueprint id. The module docstring also has that id. The theorem
docstring follows all seven current DAG proof steps, naming the existing dependencies and
explaining the full transport identification, both variance squares, pullback, universe
lift and empty cases. The main theorem retains its eight-step docstring. I removed the
false report claim that only one theorem is postponed.

H11 report correction: the table above records the actual types rather than claiming that
bare Prop fields encode coherence. I also reread every clause of the main item against the
unchanged module: small J and local smallness are the explicit binders; literal A,q,Gamma
are its pullback/internal-over-Hom definitions; `first` and `second` have the two exact
transformation-space endpoints, Kan assertions, inverse maps and homotopies; `first_formula`
fixes every simplex; `coherent` and `components` retain joint x,p variance; restriction has
actual induced maps and its four-boundary coherent square; `ConstantSourceConeFormula`
uses the specified constant-diagram mapping maps, the entire image cone mu, normalized
point insertion, and canonical composition; `small_model` asserts only smallness of the
section space. The empty cases remain admitted. I found no need to change the item's
statement or its main Lean signature. Its dependency import now reads a meaningful theorem
with the seven-step proof plan it invokes.

Additional repair searches (2026-10-17): msearch LeanFinder, query “Simplicial family of
functors induces coherent relative Hom evaluation and a map of source fixed arrow left
fibrations compatible with transport”, returned ordinary nerves, simplicial thickening
and relative morphisms, no comparison. Loogle `SSet.uliftFunctor,
SSet.Enhanced.transportFibrations` returned no hits (the side declaration is not indexed).
Mathlib grep `RelativeHomEvaluation|relativeHomEvaluation|transportFibrations` in
AlgebraicTopology returned no hits. LeanSearch “Coherent relative Hom evaluation of a
simplicially parameterized functor as a map of source fixed arrow left fibrations” returned
ordinary evaluation, simplicial-category sHomFunctor and unrelated results. The latter
is an ordinary enriched Hom functor and does not give relative quasicategorical evaluation.
Source-project and side-library rg for `relativeHom|RelativeHom` found only unrelated
relative homotopy declarations; the exact item-id grep in WeilConjectures found no match.
Kerodon 05R5, 046J and 03PD were reopened; in particular the project server explains why the chosen
transport comparisons must be retained, as the explicit comparison square now does.


Final self-check addition: the first repaired version compared the restricted epsilon maps
and the actual Phi maps but did not retain the chosen transport squares under restriction.
`RelativeHomPullback.fibrationPullback` now uses `TransportPullback` itself, including its
all-simplex over-Hom formula. `classifier_naturality` compares the same classifiers with
restriction. `sourceChange` and `targetChange` are equivalence transformations with fixed
endpoints; `arrow_square` compares the full arrow transformations. `comparison_cube` has
as two opposite faces the pullback of the old `transport_square` and the new one, and its
arrow face is exactly `arrow_square`. Its other faces therefore retain the change of
chosen source and target comparisons and the induced classified-epsilon comparison. This
closes the pullback-coherence clause without replacing the chosen transport square by a
fresh independent identification.
