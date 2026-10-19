## Worker report

Item: `def-coef-segal-presheaf-localization`; group NU; 2026-10-17 UTC.
Module: `Sheaf.CategoryTheory.SegalPresheafLocalization`.
All names below without a namespace prefix belong to
`SSet.Enhanced.SegalPresheaf`. The main declaration is
`coefficientLocalCategory`; the node lists all 71 declarations belonging to this
compound definition. This is a definition delivery: no theorem, `sorry`, axiom,
or postponed existence assertion is introduced.

### Hypotheses, universes, and clause correspondence

1. **Infinity categories and sizes.** The implementation uses the existing
   enhanced simplicial-set model, its coherent internal Hom, `mappingSpace`,
   `fullSubcomplex`, `comma`, `IsInitial`, `IsColimiting`, and `hocolim`.
   `transportDiagrams.{u,v} C false` is the existing
   `Fun(C.op, transportSpaces.{u,v})`, not another presheaf definition.
   The space universe `u` and containing universe `v` remain independent;
   the ambient simplicial-set universe is `max (u + 1) v`.
   `CartesianPresentation` starts with the small monoidal category in universe
   `u`; `ambientTotal`, `simplexBaseLift`, and `ambientProjection` give its
   actual universe inclusion. Generic definitions also make sense on arbitrary
   projections `q`; for the node one uses this classified cartesian projection.
   This does not impose an additional mathematical hypothesis on C.
2. **Left Kan extension.** `restriction f` is actual precomposition with
   `transportBaseMap f false`. `LeftKanExtension f F` consists of an actual
   initial vertex in the coherent comma category of extensions, including the
   unit. Its initiality is precisely the natural mapping-space universal
   property in the node. `leftKanExtension` reads its apex using the existing
   `Coyoneda.vertexFunctor`. No functor is chosen from a mere `Nonempty`.
3. **Day convolution.** `SpaceProducts` supplies the cartesian product functor
   characterized by its coherent right adjunction to the diagonal.
   `externalEvaluation` uses the two internal-Hom evaluation maps and this
   product; `externalProduct` is its exponential transpose.
   `DayExtension tensor` supplies the left adjoint to restriction along tensor,
   and `dayConvolution` composes it with external product. `binaryTensor`
   translates the existing Fin-2 product API. `MonoidalDayExtension.isTensor`
   requires the recorded `IsMonoidalTensorOperation p 2 tensor`, so the tensor
   is the operadic tensor, including active-transport normalization.
4. **The cartesian category C_tensor.** `CartesianPresentation.monoidal` is
   the given cocartesian presentation, required by `isMonoidal` to be a
   monoidal infinity category. `dual` is a cocartesian fibration classified by
   its pointwise opposite, with `opposite` required to satisfy
   `IsCatInfinityOpposite`. `classification` compares the actual straightening
   functors. `total` and `projection` take the opposite of that dual fibration.
   Thus their cartesian classification is the original monoidal functor,
   with fibers C^n and the interval tensor transport of the monoidal
   dependency, including empty intervals (unit). This avoids erroneously
   replacing C by C.op. `baseVertex` and `baseEdge` retain simplex orientation.
5. **Representables, spines, and their canonical map.** `representedSimplex`
   evaluates the normalized Yoneda embedding on an object of the arity-n fiber.
   `EndpointData.vertex` lies over [0], and `vertexRepresentable` is its
   Yoneda image v. `SpineFaces n` is the full incidence category of vertices
   and consecutive edges over [n]. `LabelledSpine` supplies a coherent cocone
   to the labelled n-simplex, with each object over the specified simplex and
   each leg cartesian over the specified face inclusion. Its incidence arrows
   therefore glue target to source. `representedSpine` is the colimit of that
   represented incidence diagram; the univalent coherent colimit includes
   exactly the displayed homotopy pushouts over v. `spineComparison` is the
   apex of a morphism from its universal cocone to the represented cocone,
   not an unconstrained map of presheaves.
6. **Segal condition and Q_C.** `IsSegal q Z` quantifies over every n with
   `2 ≤ n` and every such labelled cartesian spine. It uses the existing
   `YonedaLimits.OppositeImageComparisonIsEquivalence` on Z and that cocone.
   This tests the canonical evaluation map to the homotopy limit of the
   edge/vertex incidence diagram, exactly the iterated homotopy fiber product
   in the statement. `segalCategory` is its full subcomplex and
   `segalInclusion` its full inclusion. This uses spaces and homotopy limits,
   rather than strict Segal bijections of sets.
7. **J_C, a_phi, copower, and fixed-endpoint E_C.** `labelInclusion` is the
   actual fiber inclusion at arity one. `FiberExtension` is its opposite
   presheaf left Kan extension with its full adjunction. `labelColimit` is
   `hocolim` of phi on C.op. `copower` is pointwise product with the constant
   space a. For E_C the implementation uses the node's expressly equivalent
   colimit-under-endpoints description. `endpointDiagram` and `Colimit` give
   the actual two-point coproduct B = v coproduct v, including both universal
   injections. `underEndpoints` is the coherent undercategory of B.
   `EndpointData` supplies both coherent cartesian vertex-to-edge cylinders.
   `FreeEdgeData.apex_formula` fixes every edge to its normalized Yoneda
   representable; `endpoint_triangles` fixes the two structural maps to the
   Yoneda images of those cartesian cylinders, on the entire label category.
   `universalElements` is the coherent category of triples (c,phi,y(c)→phi);
   its fiber at phi is its category of elements, equivalent by normalized
   Yoneda to the classified right fibration in the node. `extension` is its
   universal left Kan extension into the undercategory. `coefficientFreeEdge`
   forgets the undercategory structure after this colimit. These are specified
   universal objects, following the existing `hocolim` convention; no
   existence theorem is asserted or required as a new hypothesis. They
   specify the canonical construction up to its universal equivalence.
8. **Local objects and local equivalences.** `IsLocal S M` quantifies over
   every s in S using existing `ProjectivePresheaf.IsLocalAt s M`, which tests
   actual precomposition on mapping spaces. `localCategory` is its full
   subcomplex. `IsLocalEquivalence S f` tests that same precomposition for
   every local M. Smallness of the set is relevant to reflector existence,
   not to these predicates, which are defined for any set without imposing
   an extra size restriction. `IsMonoidallyCompatible` tests both
   tensor(s,id_X) and tensor(id_X,s) for every generator and every X.
9. **Q_C^S.** `IsCoefficientLocal F S` is a predicate on `segalCategory q`
   testing ambient mapping-space locality for the image of S under the
   normalized `coefficientFreeEdge F`. `coefficientLocalCategory` is the full
   subcomplex inside Q_C, and `coefficientLocalInclusion` has codomain Q_C.
   The auxiliary `...For` versions factor the same predicate through a given
   functor; the recorded main declaration uses the normalized free edge.
10. **Mapping presheaf.** `mappingPresheaf F HU Z` restricts the normalized
    Hom functor in the undercategory along the represented-edge diagram.
    An object Z under B is precisely a presheaf with its two specified
    endpoints. Maps under B from an edge to Z are the homotopy fiber of
    Map(edge,Z)→Map(B,Z) at those endpoints. The coproduct property and Yoneda
    identify this with the displayed fiber of Z([1](c))→Z([0])².
    `HU` is a normalized `HomPresentation`, so this is a coherent presheaf
    with its canonical action, rather than unrelated fibers at each c.
    Restricting Z to Segal objects gives exactly the clause in the node;
    the construction itself is also meaningful for other Z.
11. **Reflectors and equivalences.** `Reflector` is a coherent left adjoint
    to the actual full inclusion, using `CoherentAdjunction` with unit,
    counit, triangle fillers, and universal comma objects.
    `SegalReflector` specializes its source to all presheaves and
    `CoefficientReflector` specializes its source to Q_C. Their inclusions
    are the two named inclusion definitions. `IsSegalEquivalence` tests
    equivalence of the reflected edge; `IsCoefficientSegalEquivalence`
    requires its input edge to lie in Q_C and tests reflection into Q_C^S.
    No reflector is claimed to exist in a case where the node only says
    “when it exists.”
12. **Two external products and S odot T.** `fiberwiseExternalProduct P p q`
    restricts `externalProduct` along the actual inclusion of the pullback
    E ×_base F into E × F. For the two cartesian simplex projections this
    has the node's aritywise values on (C×D)_tensor. In contrast,
    `coefficientExternalRelations` uses external product on C×D and the
    two actual normalized Yoneda maps. Its set is exactly the union of the
    image edges (s,id_y(d)) and (id_y(c),t), using degenerate identity edges.
    Its codomain is P(C×D), not the operadic external-product category.
    This set construction also makes sense before assuming monoidal
    compatibility; it asserts no compatibility theorem.

### Dependency declarations read and reused

The following are the recorded module names under `Sheaf.CategoryTheory`;
full namespaces of the declarations are given where necessary.

| Node / module | Declaration or interface used |
| --- | --- |
| def-coef-complete-algebroid / CompleteAlgebroid | `SSet.Enhanced.Algebroid.completeCategory`; enhanced size conventions |
| def-cbc-enhanced-diagrams-cones / EnhancedDiagramsCones | `SSet.Enhanced.mappingSpace`, `fullSubcomplex`, `comma`, `IsInitial`, `IsColimiting`, `hocolim` |
| def-coef-monoidal-infinity-category / MonoidalInfinityCategory | `monoidalSimplexBase`, `monoidalBaseVertex`, `monoidalBaseEdge`, `monoidalUnderlying`, `IsMonoidalInfinityCategory`, `IsMonoidalTensorOperation` |
| def-coef-infinity-fibrations / InfinityFibrationsOverSimplicialBases | `IsCartesianEdge`, `fiber`; the public fibration interface |
| lem-coef-space-yoneda-density / SpaceYonedaDensity | `CategoryTheory.Spaces.space_yoneda_density`; normalized representable/density conventions |
| lem-coef-infinity-presheaf-free-cocompletion / InfinityPresheafFreeCocompletion | `SSet.Presentability.infinity_presheaf_free_cocompletion`; existing presheaf small-colimit convention |
| lem-coef-infinity-yoneda-presheaf-limits / InfinityYonedaPresheafLimits | `SSet.Enhanced.YonedaLimits.HomPresentation`, `OppositeImageComparisonIsEquivalence`, `coneCylinder` |
| lem-coef-cocartesian-straightening / CocartesianStraightening | `SSet.Enhanced.CocartesianStraightening.Statement`, `coCart`, `object`, `classify` |
| lem-coef-space-transport-classification / SpaceTransportClassification | `transportSpaces`, `transportDiagrams`, `transportBaseMap`, `transportHomColumn`, normalized `HomTransport` |
| def-coef-coherent-adjunction-data / ModelInfinityDerivedAdjunction | `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction` |
| lem-coef-coherent-diagram-coyoneda / CoherentDiagramCoyoneda | `SSet.Enhanced.Coyoneda.vertexFunctor` |
| lem-coef-simplicial-presheaf-localization-comparison / SimplicialPresheafLocalizationComparison | `SSet.ProjectivePresheaf.IsLocalAt` |
| lem-cbc-enhanced-functor-cone-calculus / EnhancedFunctorConeCalculus | `SSet.Enhanced.calculusApex` |

The last four already-landed nodes are added to `stmt_deps` to reuse their
canonical interfaces instead of duplicating notions. Their node statements,
Lean records, and the used declarations were read. A graph traversal found no
path from these dependencies back to this item. No new node is needed. A subsequent live-library compilation repair is
recorded below. The original mathematical statement is unchanged.

### Edge cases and author check

- n=0 and n=1 are not extra Segal tests; the predicate starts at n=2.
  For n=2 the incidence shape is the two edges and their shared vertex,
  with separate outer vertices; its limit is the homotopy pullback specified.
- Both endpoints remain separate coproduct summands even when both use the
  same represented vertex. Neither injectivity nor distinctness of x,y is
  assumed. The undercategory retains homotopies fixing the endpoint pair.
- Empty phi has an empty category of elements, so its colimit in the
  undercategory is id_B, whose underlying presheaf is v coproduct v.
  Taking the ordinary colimit of edges would instead produce the wrong
  initial presheaf; the definition deliberately takes the undercategory
  colimit. The same construction handles disconnected and noncontractible
  a_phi; no contractibility/nonemptiness hypothesis is added.
- Empty S gives the vacuous locality predicate on Q_C. Neither locality
  nor external relations assumes generators exist. With empty S or T only
  the corresponding half of the union is empty.
- Empty tensor intervals are retained through the existing operadic tensor
  API. Cartesian projection uses the opposite of the pointwise-opposite
  classification, preserving C rather than inadvertently using C.op.
- Reflector inputs have the correct domains, and arbitrary precomposition
  maps, arbitrary Hom data, and arbitrary endpoint arrows are excluded by
  the reused normalized interfaces and the universal/triangle fields.
- Universal construction parameters carry their actual units/cocones and
  universal properties, as in the existing `hocolim`; all definition bodies
  are explicit projections, compositions, subcomplexes, pullbacks, or
  exponential transposes. There are no existence-based `Classical.choose`
  definitions, hollow data, or postponed helper theorems.
- `autoImplicit` is false. Every universe and variable is bound. Independent
  coefficient/ambient universes are retained. The maximum-universe linter
  is disabled because its syntactic max warning does not express the two
  independent size bounds of the recorded interfaces.

No statement dispute or node fault was found. This is an author check, not
an independent second reading; the worker was explicitly instructed not to
start other agents.

### Searches and source reading

Search wrapper:
`python3 /home/ubuntu/weil-launcher-nt/msearch.py NU def-coef-segal-presheaf-localization`.

| Tool | Query | Result |
| --- | --- | --- |
| leanfinder | `Segal presheaves on monoidal infinity categories fixed endpoint free edge coefficient localization` | Eight nearby strict-Segal/nerve results; no construction matching this node |
| loogle | `"Segal"` | Twelve results about strict Segal simplicial sets; not space-valued Segal presheaves |
| grep, CategoryTheory | `Segal|DayConvolution` | Twenty-one ordinary Day-convolution results; no enhanced Segal localization |
| leansearch | `Segal presheaf coefficient localization and Day convolution for infinity categories` | Eight ordinary Day-convolution results; no exact declaration |
| rg, upstream WeilConjectures and shared lean/Sheaf | `SegalPresheaf|segalPresheaf|fixedEndpoint|freeEdge|def-coef-segal-presheaf-localization` | No existing implementation; references in algebroid/Segal-locality files only |
| grep -rn, upstream WeilConjectures | `def-coef-segal-presheaf-localization` | No occurrence |
| rg, existing interfaces | `IsLocalAt` and `vertexFunctor` | Found and reused ProjectivePresheaf locality and Coyoneda decoder, respectively |
| rg, upstream declaration inventory | Segal/free-edge/localization names | No exact pre-existing definition |

Mathlib `StrictSegal` and `DayConvolution` declarations and docstrings were
read: the former uses strict simplicial-set bijections, and the latter is
ordinary categorical Day convolution. Neither gives this enhanced notion.
Original dependency nodes, recorded declarations and docstrings were read.
No declaration saying the whole node was found, so `existing` is false.

Source read: the node's source and blueprint record, together with Haugseng,
[arXiv:2311.13362v1](https://arxiv.org/html/2311.13362v1), Notation 4.1,
Definition 4.3, Notation 4.8, Section 5, Definition 8.1, Lemma 8.3,
Observations 8.6–8.9. The fixed-endpoint correction is already part of this
node and is retained, using its explicitly permitted equivalent colimit
formulation. No unit or node statement is corrected.

### Validation

All compilation is through the prescribed `scompile.py` wrapper, against the
published library with its side-project overlay. The sandbox probe and the
actual module both compiled cleanly, without errors or warnings. No global
build or live-source edit was performed. Node JSON uses one-space indentation,
UTF-8 and a final newline. Its `lean.statement` is the main signature extracted
from the module, and `lean.declarations` lists all its declarations. The item also adds the four existing helper dependencies above and the
transitive straightening dependency repaired below.

## Dependency modules

`lem-coef-space-valued-straightening`: after the first successful dry run,
the live overlay was refreshed and the push-time check twice failed on
`SpaceValuedStraightening.lean:64:7` with `lean.dependsOnNoncomputable`: its
`Diagrams` abbreviation depends on the now noncomputable `smallSpaces`. The
recorded module was therefore unusable in the current dependency graph.
Following §1(B), this delivery includes that dependency module at its recorded
path and a lean-only update to its node. The current source was obtained with
`scompile.py --source Sheaf.CategoryTheory.SpaceValuedStraightening`; the
sole source change is `abbrev Diagrams` → `noncomputable abbrev Diagrams`.
All data, signatures, definitions, the named theorem with its full source/proof
docstring, and its existing `sorry` are preserved. The node's mathematical
statement and every other field outside `lean` remain unchanged. The item
names this already transitive dependency directly in `stmt_deps` to register
the repair. This is a compilation modifier repair, not a statement correction
or an alternative straightening construction.

The same refreshed `smallSpaces` implementation required marking the owning
module's `restriction` as `noncomputable` too. Its body and signature are
unchanged. The dependency closure check (639 nodes) found no cycle from the
added straightening dependency back to the item.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
