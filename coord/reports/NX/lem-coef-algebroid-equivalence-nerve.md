## Worker report

Item: `lem-coef-algebroid-equivalence-nerve`; group NX; stage 2.
Module: `Sheaf.CategoryTheory.AlgebroidEquivalenceNerve`.
Main declaration: `SSet.Enhanced.Algebroid.algebroid_equivalence_nerve`.

The module states the entire equivalence-nerve calculus on the recorded operadic
algebroids. Definitions have actual data. All eight theorem proofs are `sorry`;
their source and proof instructions are in their docstrings. The main docstring
includes the node's fourteen proof steps. There is no statement correction and
no STATEMENT-DISPUTED finding.

The source read is Gepner--Haugseng, arXiv:1312.3178v4,
https://arxiv.org/html/1312.3178v4, Sections 5.1--5.3: Lemma 5.1.2,
Definition 5.1.16, Proposition 5.1.17, the groupoid condition in 5.2.3 and
Corollary 5.2.7, and the results of 5.3 ending in Proposition 5.3.6.
In particular, 5.1.16 defines the invertible subspace by the component image of
evaluation from coherent equivalences. `invertibleUnits` uses that convention;
the theorem asserts the stronger, non-tautological equivalence onto that whole
subspace, including every homotopy group.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| V presentably monoidal | `[Quasicategory E]`, `p : E ⟶ monoidalSimplexBase`, `hp : IsPresentablyMonoidal.{u,v} p`; the recorded predicate includes the monoidal operad, presentability, and preservation of all small colimits separately in both tensor variables. |
| Use the recorded algebroids | `total.{u,v} p`, with the recorded universal point family; no new algebra category is substituted. `unit : UnitSection p` supplies the unit section used by the recorded `unitAlgebroid` and `unitCosimplicial`. This is the unit data of the monoidal category, not a completeness or symmetry assumption. |
| Object space U(C) | `objects A` is the literal fiber of `universalFamily.hom` over `A.val.space`. `ObjectPoint A` is its vertex description with the projection equation. |
| I_n(C) = Map(E^n,C) | `nerve` restricts `nerveBifunctor`, the recorded coherent Yoneda Hom pairing, along the recorded `unitCosimplicial`. The prerequisite's `iotaLevel` is reused for the right-pinched representative of the same mapping space. |
| E cosimplicial and I simplicial | `unitIndexMap`, `nerveSource`, and `nerveBifunctor` are maps of simplicial sets on the entire lifted simplex nerve; all operators, including degeneracies and higher compatibility strings, are present. |
| I(C) is the realization | The recorded `iota unit A` is reused. The first conjunct `IsNerveRealization.{u,v} unit` gives the colimit universal property with precisely this apex. Its augmented bifunctor restricts exactly to `nerveBifunctor`. Thus this is also coherent in every higher algebroid simplex. |
| I_S uses increasing enumeration | `GeometricDescent.IsGroupoidCover D` expresses the injective monotone inclusions by their ranges, hence their increasing enumerations. Corner values are the degrees of those subsets. |
| Natural I_0(C) ≃ U(C) | `objectEvaluationResolution unit r₀ A` maps by `objectEvaluationSource` to the fixed-endpoint arrow model of Map(E^0,A), and by `objectEvaluationTarget` to `objects A`; both legs are asserted weak equivalences. `nervePinch` is the canonical prism comparison from the prerequisite's right-pinched model, and the theorem supplies its homotopy inverse. These are evaluation maps, not unrelated equivalences of abstract spaces. |
| Every singleton-intersection cover gives a pullback | `IsEquivalenceGroupoid unit A` quantifies over every `D` satisfying the recorded `IsGroupoidCover`. `IsLimitingConeAt squareLegs` is the recorded enhanced limit universal property with its entire cone fixed by the restriction diagram. This includes nonadjacent subsets and interior pivots. |
| Complete iff U(C) → I(C) is an equivalence | The `IsComplete` equivalence tests the canonical augmentation on the common evaluation resolution: `objectEvaluationSource ≫ q ≫ sSetTopAdj.unit.app _ ≫ completenessMap`. Both legs of the resolution are weak equivalences, so this is exactly the canonical map from U in spaces. The inverse q is tied to the explicit pinch map by both homotopies. |
| I_1 fiber over (x,y) | `equivalenceFiber` is Map in the actual two-pointed algebroid category from the two labeled objects of E^1 to `(A,x,y)`. Since this category is pulled back from the universal power family, its mapping spaces retain the endpoint paths of the homotopy fiber. They do not impose strict equality of images with x and y. |
| Fiber is the invertible components in Map_V(1,C(x,y)) | `unitMaps` is the recorded `monoidalRelativeMap` in the fiber over [1], from the recorded unit to the recorded `homObject`. `equivalenceEvaluation` is uniquely fixed by evaluation on `pairParameter` on every simplex and the recorded pinch prism. The theorem factors it through `invertibleUnits`, with that exact factor asserted a weak equivalence. |
| FF induces equivalences on these fibers | For every edge in `pointedTotal p 2` whose forgotten edge is `IsFullyFaithful`, both `basedArrowLeg` evaluations are weak equivalences. Their source is the canonical arrow-resolution mapping space from the fixed labeled E^1. The zero leg forgets the target map and the one leg is postcomposition; this is the canonical induced map as a span, matching the prerequisite's convention. |
| ES iff every target object is equivalent to an image | `IsEssentiallySurjective unit (algebroidArrow f) ↔ EveryObjectInImage unit r₁ f`. The latter quantifies over all target points and gives a lift along the actual object-space edge, followed by a point of the corresponding equivalence fiber. Its initial endpoint is a source object and its final endpoint is its image, with the legitimate transport paths. |
| Equivalent formulation: π_0 I(F) surjective | The recorded `IsEssentiallySurjective` is precisely surjectivity of `componentsMap` of the target leg `iotaMorphismLeg`. That recorded definition is used directly. |
| FF and ES imply I(F) equivalence | The implication concludes `IsWeakHomotopyEquivalence (iotaMorphismLeg unit (algebroidArrow f) 1)`, the recorded canonical postcomposition span's target leg. |
| FF and object-space equivalence imply equivalence in Algd(V) | `IsFullyFaithful f → IsEquivalenceEdge transportSpaces f.val.space → IsEquivalenceEdge (total p) f`. Neither algebroid is assumed complete. |
| Compose on either side with an object equivalence | The final conjunct gives `IsEnrichedAction` and `IsEquivalenceEdge E e` for precomposition on C(y,z) → C(x,z) and postcomposition on C(z,x) → C(z,y). These are equivalences of the enriched objects themselves. |
| All statements natural in algebroid maps | `nerveBifunctor` contains the whole algebroid variable, and `IsNerveRealization` extends that bifunctor to the augmented index. Pointed spaces use the actual universal family in all degrees; evaluation is normalized on every simplex, and comparison maps are the actual pullback, prism, and evaluation maps. The actions use the actual algebra operations and unitors. Consequently the comparisons are the coherent evaluation/restriction/postcomposition comparisons, rather than arbitrary equivalences selected object by object. |

The enriched-action predicate specifies the operations, rather than merely
asserting existence of some equivalence between the same endpoints. Its inert
squares fix both tensor factors, its active square fixes algebra composition,
and the cocartesian edge over sigma_i inserts the tensor unit. The two triangles
with identity long edge fix both the remaining factor and the unitor. This
prevents replacing composition by an unrelated invertible edge.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: `total`, `universalFamily`,
  `transportSpaces`, `UnitSection`, `unitCosimplicial`, `unitAlgebroid`,
  `familyPower`, `familyDiagram`, `FamilySimplex`, `pairParameter`, `homObject`,
  `iotaLevel`, `iota`, `completenessMap`, `IsComplete`, `IsFullyFaithful`,
  `IsEssentiallySurjective`, `iotaMorphismLeg`, `IsPresentablyMonoidal`.
  The full source and recorded node signature were read, including the current
  source returned by `scompile.py --source`.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`:
  `CategoryTheory.Spaces.yonedaPairing`; explicit pre/postcomposition in the
  singular-realization rigidification enrichment, retaining higher simplices.
  Its already-landed definition node is added to `stmt_deps`.
- `Sheaf.CategoryTheory.SpaceGeometricDescent`: `index`, `indexMap`,
  `IsGroupoidCover`, `squareLegs`, `IsLimitingConeAt`, `AugmentedIndex`,
  `point`, and `IsColimitCocone`. This already-landed node is added to
  `stmt_deps`. Its cone tests work in any ambient simplicial category, so they
  apply directly to the canonical Yoneda space category without copying its
  specialized `IsGroupoidObject` predicate or identifying different enrichments.
- The inherited enhanced-diagram declarations `mappingSpace`, `mappingSpaceMap`,
  `fiber`, `fullSubcomplex`, `evaluation`, `constantDiagrams`, `diagramVertex`,
  `IsEquivalenceEdge`, `transportSourceTarget`, and the inherited monoidal
  declarations `monoidalRelativeMap`, `monoidalRelativeMapInclusion`,
  `monoidalRho`, `monoidalTensorArrow`, `IsCocartesianEdge` are reused.
- The inherited `RightPinchComparison` interface supplies `arrowMappingSpace`,
  its inclusion and `rightPinchPrism`. Its theorem gives existence of the
  normalized map under a quasicategory hypothesis. Here `exists_nervePinch`
  states the normalization's existence and uniqueness for arbitrary simplicial
  sets, before the fibrancy assertions, so the helper can be defined without
  adding a quasicategory assumption to an algebra's raw model.

All already-stated proof dependencies are imported, privately when used only
by the planned proof: `PointwiseCocartesianTransport`,
`CoherentDiagramCoyoneda`, `CoarseNerveGluing`,
`SegalSpaceInnerAnodyneLocality`, `SegalInverseEvaluation`, and
`ContractibleHomotopyFiberEquivalence`. `SpaceGeometricDescent` and
`CompleteAlgebroid` are public because they also occur in the statement.
The remaining proof-only prerequisites have no recorded module yet.

Named postponed proofs, all owned and listed in this node's `lean.declarations`:
`reverseString_naturality`, `nerveSourceValue_naturality`,
`nerveTransportValue_compatible`, `pointedTotal_over`,
`exists_equivalenceEvaluation`, `objectEvaluation_conditions`,
`exists_nervePinch`, and `algebroid_equivalence_nerve`.
The two maps defined using `Classical.choose` come from unique, completely
specified formulas on every simplex. No definition chooses an arbitrary map
from a mere existence statement. Pullback equations and simplicial laws use
named proof obligations; all remaining data are literal constructions.
These are helpers of the owning node, as authorized by the human update;
there are no new nodes and no dependency-interface repairs.

Edge cases checked before and during the second pass:

- Empty object space: objectwise clauses are vacuous; maps out of an empty
  algebroid are still covered. ES into a nonempty target fails, while the empty
  target/source case is included in the realization assertion.
- x = y is permitted; the fiber retains the entire automorphism space.
- n = 0, repeated vertices, degeneracies, and singleton subsets are included.
  Groupoid covers are not restricted to consecutive intervals or endpoint pivots.
- Finite labels live in E^0 and E^1 only. No target algebroid is assumed to
  have a nonempty object space. The two E^1 labels are required to be distinct
  on object components, not distinct merely as representations of points.
- FF alone is used for fiber comparisons; ES is imposed only in the realization
  implication. Completeness and symmetry are never added as hypotheses.
- The enriched-action conclusion is in E over [1], not merely on unit-valued
  mapping spaces or their components.
- The coefficient universes remain independent u and v, using the prerequisite's
  max(u+1,v) and containing-universe lifts. No equality of universes is imposed.
  `autoImplicit false` is set. Universe annotations resolve the noninjective max;
  the universe linter is disabled because distinct universes occur under max.

Search log (no exact existing statement was found):

- `msearch.py ... leanfinder "The equivalence nerve of an enriched infinity
  algebroid is a groupoid object and fully faithful essentially surjective maps
  induce weak equivalences"`: eight ordinary nerve/category hits, including
  `nerve.fullyFaithfulNerveFunctor₂`, `nerveFunctor.fullyfaithful`, and ordinary
  truncation comparisons. Their signatures do not state this enriched result.
- `msearch.py ... loogle '"EnrichedCategory", "nerve"'`: zero hits.
- `msearch.py ... grep 'algebroid|equivalenceNerve|IsGroupoidObject'
  CategoryTheory`: zero Mathlib hits.
- `msearch.py ... leansearch "The equivalence nerve of an enriched infinity
  category is a groupoid object and fully faithful essentially surjective
  functors induce equivalences"`: eight hits. `SimplicialNerve`, ordinary nerve
  full faithfulness, ordinary essential-image equivalence, and ordinary
  equivalence/groupoid lemmas; none is an infinity-algebroid theorem.
- `rg` in the read-only upstream `WeilConjectures` and shared `lean/Sheaf`
  for algebroid/equivalence-nerve/groupoid-object names: the usable interfaces
  are `CompleteAlgebroid` and `SpaceGeometricDescent`; no item theorem.
- The required upstream grep for `lem-coef-algebroid-equivalence-nerve` found
  no existing declaration. Searches for the chosen main/helper names in the
  upstream source, shared Lean, and upstream-name index found no collision.
- The recorded node searches and the full dependency node/Lean record were
  also read. No private replacement of an existing dependency was introduced.

Validation is through the required `scompile.py` wrapper only. The final file
is compiled in both the sandbox and its intended library module path; all
ordinary warnings must be absent. The delivery wrapper's dry run and actual
delivery provide the final server preflight and per-file compilation.

## Second reading by NX

This is the author's second pass, not a claim of an independent worker review.
The dispatch explicitly requests direct delivery and reserves the independent
reading for the maintainer; it also forbids starting other agents.

I reopened the node and the file and compared every clause using the table
above. The first pass needed two additions: the realization now has its explicit
colimit universal property in a bifunctor on the full algebroid variable, and
the enriched composition clause now specifies the tensor operations and unitors
through inert/active squares and identity triangles. I checked that the latter
acts on the enriched hom objects, that the fibers retain endpoint paths, and
that the groupoid test includes arbitrary singleton-intersection covers. The
invertible-subspace convention was checked against GH Definition 5.1.16.
The recorded raw mapping spaces, FF/ES definitions, and object-space universe
conventions were retained. A namespace reference in the singular-realization
unit and an ambiguous max-universe inference were corrected during compilation.
No mismatch requiring a node statement change was found.

## New nodes

The returned split requires the terminal-space model to expose its canonical pairing data. I added
`def-coef-algebroid-terminal-space-pairing`, whose module defines the actual coherent Yoneda
pairing in the terminal space model. The existing `lem-coef-infinity-pinch-comparison` node
already supplies the right-pinch comparison and its homotopy inverse. The item cites the new
definition in `stmt_deps`; its statement is unchanged.

## Split repair

The retained node proof already contains the maintainer's short fourteen-step route (every
non-elementary step is below the 2,000-character stage-1 limit). I preserved that route and added
the concrete terminal-space pairing definition as the missing helper interface. The module proof
docstring was regenerated to match the retained fourteen proof steps.

The added definition compiles as `Sheaf.CategoryTheory.AlgebroidTerminalSpacePairing`,
`SSet.Enhanced.Algebroid.terminalSpacePairing`. Its data is the recorded canonical pairing;
no arbitrary choice or replacement map is introduced.

## Duplicate projection repair

The returned delivery reported that this module redeclared
`SSet.Enhanced.Algebroid.objectProjection`, already supplied by
`Sheaf.CategoryTheory.AlgebroidObjectSpaceFibration`. I imported that module, removed the
local duplicate, and use its canonical `SSet.Enhanced.Algebroid.totalProjection` abbreviation
in `pointedTotal`. The node retains its acyclic recorded `stmt_deps`; adding the object-space-fibration node there would close the pre-existing reverse proof-dependency cycle (that node lists this item in `proof_deps`). The imported module is therefore a lean interface repair, and this node's `lean.declarations` no longer claims the imported `objectProjection`.
The existing projection has the same total-algebroid-to-transport-spaces map used here:
`objectProjection universalFamily.hom p`, definitionally exposed as `totalProjection p`.
The repaired module compiles with `scompile.py` and the delivery dry run is the remaining check.

Searches for the helper notion were run with `msearch.py`: `leansearch`, `leanfinder`, `loogle`,
and `grep` found only Mathlib's ordinary `CategoryTheory.yonedaPairing`; the coherent simplicial
pairing is the project interface used here.

## Re-split repair audit

The returned stage-1 instruction identifies the original terminal coefficient construction and
its total-fibration assembly as the overloaded arguments. The retained fourteen-step route already
replaces those paragraphs by short applications of the existing nodes: `lem-coef-algebroid-segal-
localization-model` and `lem-coef-operadic-day-convolution` give the terminal Day extension and
its coherent adjunction; `lem-coef-cocartesian-straightening` and
`lem-coef-infinity-pointwise-cocartesian-transport` give the variable-object-space mapping
fibres; `lem-coef-many-object-operad-accessibility` and `lem-coef-operadic-change-enrichment`
give the fixed-operad fibre adjunction; and `lem-coef-cocartesian-relative-right-adjoint` gives
its coherent assembly over object spaces. The finite-set unit comparison is then cited through
`lem-coef-operadic-day-convolution`. Each of these applications is a separate elementary step
in the retained route (all are below 2,000 characters), while the theorem statement and its Lean
record remain unchanged. No independent notion was missing: the existing DAG nodes state every
intermediate argument, so no additional helper node is introduced.
