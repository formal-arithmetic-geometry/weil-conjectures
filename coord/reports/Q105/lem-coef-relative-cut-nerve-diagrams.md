## Worker report

Item: `lem-coef-relative-cut-nerve-diagrams`. Group Q105. Stage 2 only.

The delivery states the relative coherent-diagram theorem and its remaining clauses
in `lean/Sheaf/CategoryTheory/RelativeCutNerveDiagrams.lean`, namespace
`SSet.Enhanced.RelativeCut`. The original informal statement is unchanged.
The principal theorem is `relative_cut_nerve_diagrams`; the node's `lean.declarations`
lists all parts, including the canonical-map helpers and their well-definedness lemmas.
Every postponed assertion is a named theorem with `sorry` and a source/proof docstring.
The principal theorem's docstring also includes the complete nineteen-step DAG proof.

### Hypotheses and clauses

| Informal datum or clause | Lean rendering |
| --- | --- |
| Small ordinary category with independent object/morphism sizes | `I : Type u`, `[Category.{v} I]`, transported by Mathlib's `AsSmall.{w} I` to the common ambient universe `max u v w`. There is no equation between `u` and `v`. |
| Small quasicategory and specified relative isofibration | `E : SSet.{max u v w}`, `p : E ⟶ nerve (AsSmall I)`, `hp : IsIsofibration p`. The dependency predicate includes both quasicategory conditions, inner-fibration lifting, and exact source-fixed equivalence lifting. |
| Coherent realization and coherent nerve | The recorded `CoherentNerveComparisonStatement N`: its actual `rigidification`, `adjunction`, simplex-realization and simplex-map fields, and `CoherentNerve.nerveFunctor`. The theorem works for any such comparison datum. |
| Any simplicial indexing set and specified base diagram | The universal `S : SSet`, `b : S ⟶ nerve (AsSmall I)` binders. No quasicategory hypothesis is imposed on `S`. |
| Strict fiber at the entire base diagram | `lifts p b := (calculusFiber ((ihom S).map p) (diagramVertex b)).toSSet`. Membership fixes the entire base simplex in every degree. |
| A vertex object in each specified base fiber | `x : (core (lifts p (vertexInclusion S ≫ b))).toSSet _⦋0⦌`. `vertex_tuple_product` states the canonical evaluation isomorphism with the product over `v : S₀` of the cores of `calculusFiber p (b.app _ v)`. Thus this ranges over every tuple in the statement, including the empty tuple. |
| Identifications at vertices retained | `fixedVertexSpace p b x := homotopyFiber (coreMap (vertexRestriction p b)) x`. It is the recorded path-space homotopy fiber, not the strict fiber. Its path coordinate and all higher simplices remain part of the data. |
| A locally Kan relative presentation exists | First conjunct of `relative_cut_nerve_diagrams`: `Nonempty (Presentation N (Cat.of (AsSmall I)) p)`. `Presentation` contains `A : SCat`, `locallyKan`, enriched `pi : A ⟶ discreteCategory I`, the specified `e`, `IsFunctorEquivalence e`, and `over` as an exact equation with `p`. |
| Ordinary/coherent base nerves identified canonically | `ordinaryNerveMap` uses the recorded normalized `N.discrete_nerve` and evaluation of discrete-enrichment arrows by `discreteForget`. It is not a freely chosen map. `Presentation.projection` is exactly `nerveFunctor.map pi ≫ ordinaryNerveMap`. |
| Endpoints in the presentation are the images of the original tuple | `imageTuple p P.projection P.e P.over b x`; its actual map is postcomposition by `e` on strict vertex lifts. No fresh endpoint choices or mere existence choices are made. |
| Cut-poset nerves | `cutMap F m σ a c` is precisely the enriched functor's hom map from `SimplicialCategory.sHom (.mk (ULift.up a)) (.mk (ULift.up c))`. Mathlib defines this hom as the nerve of `SimplicialThickening.Path`: endpoint-containing subsets of the closed interval, ordered by inclusion. |
| Target objects are the prescribed endpoint objects | `exact_cut_description` decodes each exact family uniquely and identifies the object at every simplex vertex with evaluation of the specified tuple at that vertex. Applying this with `imageTuple` gives exactly `e(x_{σ(a)})` and `e(x_{σ(c)})`. |
| Maps lie over the composite base arrow | The final clause of `exact_cut_description` quantifies over every cut simplex `τ` and says its image under `pi.map` is `HEq` to `(b.app _ σ).map (homOfLE hac)`. `HEq` accounts only for the equal endpoint objects in the dependent hom types. |
| All faces, degeneracies, identities, union compositions and relations | A whole family is a simplicial map `F : S ⟶ nerveFunctor.obj A`. Its simplex value is Mathlib's actual `EnrichedFunctor`; the enriched functor laws include identities and composition, whose source composition is union. Naturality of `F` includes every simplex operator; `SimplicialThickening.functor` acts on cuts by direct image. This uses the existing coherent-nerve definition instead of a private weakened compatibility predicate. |
| Actual global enriched map from coherent realization | `enriched_cut_gluing` gives the unique `f : N.rigidification.obj S ⟶ A` whose adjoint is the decoded whole cut family, and states its exact relative equation after the normalized ordinary-nerve identification. |
| Derived compatible-map space, with all higher compatibilities | `diagramCore T C` is the core of the entire internal-hom quasicategory. `cutSquare` is its full augmented restriction/base square for `S` and the discrete vertices. `derivedCuts` is the total homotopy fiber of its specified-path comparison, at the constant-base boundary point `vertexBoundary p b x`. This is the symmetric total-fiber model of proof steps 3–9. It retains both relative identifications and their coherence. |
| Relation to exact cut-map families | `exactCuts` is explicitly distinguished from `derivedCuts`. The second universal clause of the main theorem states that the specified `exactToDerived` is a weak equivalence for a locally Kan presentation over the ordinary base. Thus an ordinary strict compatibility construction is not silently declared derived. |
| Natural equivalence to the original fixed lift space | For every presentation, every `S,b,x`, the main theorem asserts `IsWeakHomotopyEquivalence (presentationComparison P ... b x)`. This map is defined by postcomposition with the specified `e`, followed by the constant-base comparison; `fiberMap` acts on both the object and the entire identification path. |
| Independence of presentation | The preceding assertion is for every `P`, giving the canonical weak-equivalence zigzag through the same original `fixedVertexSpace p b x` for any two presentations. |
| Coherent equivalence of complete systems | `complete_cut_system_invariance` takes a `KanCoherentCube` between the full augmented diagram-core squares. These four spaces are spaces of whole coherent families, already including every restriction/composition relation. The cube specifies all side homotopies and their two-dimensional coherence. It produces a weak equivalence of total fibers, characterized by `IsInducedFiberMap`; every induced choice is a weak equivalence and all are homotopic. It does not take separate equivalences of the individual `A(x,y)` as sufficient input. |
| Restriction over the base | `presentation_comparison_naturality` quantifies over every `i : T ⟶ S`, using `b` and the pulled-back base diagram `i ≫ b`. The fixed and derived restriction maps are actual path-coordinate restrictions. Its `HEq` only transports the equality of the two images of the restricted tuple. `strict_to_derived_naturality` also states the underlying comparison square. |
| Change of vertex data by equivalences | `presentation_vertex_naturality` takes an actual edge `η : Δ[1] ⟶ core (lifts p (V ≫ b))` with both endpoints prescribed. The two transport maps must satisfy `FiberTransport`, which fixes their first coordinate and supplies the entire composition triangle. Both are weak equivalences, and the comparison square commutes by an actual simplicial homotopy. |
| Coherent parameters `S × K → S → N(I)` | The same main comparison is quantified over every small indexing simplicial set, in particular `S ⊗ K`, with base `fst S K ≫ b`. Restriction naturality is quantified over every simplicial map, in particular all parameter operators and maps between these products. Internal homs, path maps and the transport triangles retain all parameter degrees. No pointwise-only replacement is used. |
| No completeness, cocompleteness or presentability of `E` | No such binder, instance or assumption occurs. Only the stated isofibration hypotheses and the chosen infrastructure are used. |

The full augmented mapping-core square is an alternative concrete derived model to
the skeletal attachment diagram J in proof steps 10–18. It is precisely the total-fiber
model specified by proof step 9. The exact-family comparison is stated as a theorem;
its docstring supplies the fixed-object/cubical-attachment justification, and the
complete recorded DAG proof supplies the explicit J and the tower argument for stage 3.

### Canonical constructions and postponed proofs

All definition data are written out using the dependency constructions. Subcomplex
membership and coherence proofs needed by those data have separately named theorems.
`fiberMap` specifies the object coordinate and sends the entire path by the supplied
base map. `strictFiberComparison` supplies the actual constant path. `vertexBoundary`
is the recorded canonical homotopy-pullback comparison with fixed base coordinate.
`boundaryRestriction` is the recorded path-pullback map with its three restriction
coordinates. `tupleRestriction` alone uses `Classical.choose`: its theorem is an
`∃!` with the precise underlying-diagram equation, which determines the map uniquely
through the monic inclusion. It is not data chosen from an undetermined existence.

### Dependencies used

Public statement dependencies and their actual recorded interfaces follow. Original
statement dependencies are retained; the added dependencies already have landed Lean
records. No dependency record is replaced.

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones`, `SSet.Enhanced.coneCategory`.
- `lem-coef-coherent-nerve-comparison`: `Sheaf.CategoryTheory.CoherentNerveComparison`, `CategoryTheory.coherent_nerve_comparison`.
- `lem-coef-infinity-isofibration-exponentiation`: `Sheaf.CategoryTheory.IsofibrationExponentiation`, `SSet.Enhanced.isofibration_exponentiation`.
- `lem-coef-free-factor-hammock-pushout`: `Sheaf.CategoryTheory.FreeFactorHammockPushout`, `CategoryTheory.FreeFactorPushout.free_factor_hammock_pushout`.
- `lem-coef-coherent-vertex-equivalence-lifts`: `Sheaf.CategoryTheory.CoherentVertexEquivalenceLifts`, `SSet.Enhanced.coherent_vertex_equivalence_lifts`.
- `lem-cbc-enhanced-functor-cone-calculus`: `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, `SSet.Enhanced.enhanced_functor_cone_calculus`.
- `lem-coef-infinity-isofibration-pullback-limit`: `Sheaf.CategoryTheory.IsofibrationPullbackLimit`, `SSet.Enhanced.isofibration_pullback_limit`.
- `lem-coef-spaces-homotopy-fiber-detection`: `Sheaf.CategoryTheory.SpacesHomotopyFiberDetection`, `SSet.Enhanced.isWeakHomotopyEquivalence_iff_homotopyFiber_maps`.
- `lem-coef-infinity-kan-homotopy-coherent-cube-invariance`: `Sheaf.CategoryTheory.InfinityKanHomotopyCoherentCubeInvariance`, `SSet.Enhanced.kan_homotopy_coherent_cube_invariance`.
- `def-coef-infinity-relative-cone`: `Sheaf.CategoryTheory.RelativeInfinityCone`, `SSet.Enhanced.IsRelativeColimitDiagram`.
- `lem-coef-kan-homotopy-pullback-invariance`: `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`, `SSet.Enhanced.kan_homotopy_pullback_invariance`.
- `lem-coef-kan-homotopy-commuting-pullback-invariance`: `Sheaf.CategoryTheory.KanHomotopyCommutingPullbackInvariance`, `SSet.Enhanced.kan_homotopy_commuting_pullback_invariance`.

In particular the reused auxiliary declarations are `core`, `diagramVertex`,
`evaluation`, `homotopyFiber`, `IsFunctorEquivalence`, `IsWeakHomotopyEquivalence`;
`SCat`, `CoherentNerve.hom`, `CoherentNerveComparisonStatement`;
`IsIsofibration`; `discreteCategory`; `vertexDiscrete`, `vertexInclusion`;
`calculusFiber`; `coreMap`; `homotopyFiberProjection`, `homotopyFiberPath`,
`IsInducedFiberMap`; `KanCubeSquare`, `KanCoherentCube`;
`homotopyPullbackComparison`; `simplicialHomotopyPullbackMap`;
and `CoherentPathModelComparison`. Their defining declarations/docstrings were read.
Mathlib's `CategoryTheory.Nerve.quasicategory` supplies the ordinary-nerve hypothesis;
no extra hypothesis or second theorem for that existing fact is introduced.

Available recorded proof modules are also imported nonpublicly, including the
cosimplicial-frame, fixed-object, undercategory, cubical-attachment, model-localization,
cofinality and tower-limit modules. The two Mathlib proof leaves use Skeleton and
Degenerate. The proof-only `lem-coef-infinity-cofinality-space-test` has no recorded
Lean module, and so supplies no import. No statement depends on a missing interface.

### Edge cases checked

- Empty S: the vertex coproduct is empty and the vertex product is the empty product.
  No Nonempty binder excludes it; the internal hom out of the empty simplicial set
  is terminal. The canonical comparisons include this case.
- Empty E or an empty lift fiber: no lift is chosen in the definitions. Given a
  vertex tuple there may be no extension, in which case the fixed/derived lift
  spaces may be empty. No artificial basepoint in the total lift space is required.
- Dimension zero: the only cut has equal endpoints and is the identity. There is no
  negative-dimensional mapping cube; the proof explicitly treats object attachments
  separately. Dimension one has a point cut nerve and no boundary condition.
- Repeated vertices, loops, degenerate simplices and collapsed intervals: there is
  no distinctness hypothesis. The native direct-image functor turns a collapsed
  interval into the singleton identity, and composition is union. Fixed-object
  labels are allowed to have equal images in A.
- Nontrivial base automorphisms: the total boundary homotopy fiber retains the
  compatibility path over the base, rather than replacing vertical vertex
  identifications by arbitrary absolute identifications.
- A presentation projection need not be an isofibration. No such assumption is
  present in the derived model or the comparison theorem.
- All universes are explicit, `autoImplicit` is false, and the base's object and
  morphism universes need not agree. The auxiliary common-size constructions are
  applied only after the explicit standard universe transport.

### Searches

- `msearch.py ... leanfinder "Homotopy coherent diagrams with fixed vertices over an ordinary nerve are modeled by derived compatible maps of cut poset nerves"`: eight related ordinary-nerve results, no exact relative derived fixed-vertex theorem.
- `msearch.py ... loogle "SimplicialNerve, EnrichedFunctor"`: no match; the service did not resolve SimplicialNerve in that query. This result alone was not treated as evidence of absence.
- `msearch.py ... leansearch "Relative coherent diagrams with fixed vertices and derived cut maps"`: eight results (relative morphisms, ordinary squares, diagrams of cocones), none states the item.
- `msearch.py ... grep "relativeCut|cutNerve|SimplicialNerve" AlgebraicTopology`: found Mathlib's actual SimplicialNerve construction, reused here; no exact relative theorem.
- `rg -n 'relativeCut|relative_cut|cutNerve|cut_nerve'` in upstream WeilConjectures and shared `lean/Sheaf`: no exact existing theorem. `rg -n 'lem-coef-relative-cut-nerve-diagrams'` in upstream WeilConjectures also found no declaration for this item.
- Source inspection of Mathlib's SimplicialNerve, SimplicialSet/Nerve,
  Quasicategory/Nerve, Subcomplex and Category/ULift located the exact native
  constructions used, including the existing ordinary-nerve quasicategory instance.
- The recorded HTT source was consulted online. The node itself explains that the
  full relative theorem is an extracted formulation, not one verbatim HTT theorem.

### Validation and rereading

The single delivered module was compiled repeatedly through the prescribed
`scompile.py` wrapper. Initial elaboration and line-length issues were repaired.
No global build, direct Lean invocation, direct Git command or live-library edit
was used. Final compile and delivery-preflight outcomes are recorded below.

A self-reading checked the relative base equation, exact tuple images, both path
coordinates, full simplicial compatibility, empty and repeated-vertex cases, and
independent universes. The dispatcher forbids starting another agent; the independent
review is the maintainer's delivery review, as the brief specifies. No independent
second-reader result is claimed here.

## New nodes

None. The presentation, cut-family and comparison helpers belong to the notion
being stated by this item. Their declarations are all listed in this node's Lean
record. Existing notions were imported from their owning landed nodes.

## Dependency modules

None. No dependency interface required replacement.

No statement correction and no STATEMENT-DISPUTED issue.

### Final check results

- `scompile.py Q105 lem-coef-relative-cut-nerve-diagrams lean/Sheaf/CategoryTheory/RelativeCutNerveDiagrams.lean`: clean sandbox and library compilation, no errors or warnings.
- `deliver2.py Q105 lem-coef-relative-cut-nerve-diagrams --no-push`: `OK (dry run): commit 71c5726789 passes the preflight and compiles; nothing pushed`. This compiled the final Lean/node snapshot, including the full DAG proof docstring and final public imports.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
