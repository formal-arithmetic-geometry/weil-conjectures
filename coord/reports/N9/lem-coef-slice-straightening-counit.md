# Stage-2 delivery: lem-coef-slice-straightening-counit

## Worker report

The delivery states the reviewed node in `Sheaf.CategoryTheory.SliceStraighteningCounit`.
The main declaration is `SSet.SliceStraightening.slice_straightening_counit`;
`slice_straightening_counit_naturality` records its naturality. The module also constructs
its owning notion's cone evaluation, enriched pushout map, representable presheaves,
actual enriched transformations, and the canonical Q-realized fiber inclusion.
Nothing is proved: all named theorem bodies are `sorry`. All definitions have data;
there is no data-valued `sorry` and no selection of an arbitrary weak equivalence.
The node copy changes only `lean`, retaining the reviewed five-step proof and dependencies.

The previous BLOCKED message concerned a supposed stage-1 re-split. Reading the current
node and Q89's report shows that Q89 supplied the stage-1 split, with no Lean declaration.
This delivery is its first stage-2 statement, and leaves that split unchanged.

### Hypothesis and clause correspondence

- The fixed, sufficiently large universe is the explicit `universe u`. All simplicial
  sets, joins, fibers and mapping sets are `SSet.{u}`. Enriched presheaf collections
  live in the containing universe used by the recorded presentation. No object/morphism
  universe equality, smallness instance, fibrancy assumption or nonemptiness is added.
- Small quasicategories C and K are `(C K : SSet.{u}) [Quasicategory C]
  [Quasicategory K]`. The named vertex and map are `(c : C _⦋0⦌)` and `(v : K ⟶ C)`.
- E is exactly `total v c`, the categorical pullback of v and
  `Enhanced.joinSliceProjection (yonedaEquiv.symm c)`. q is `projection v c`, its first
  projection. The categorical pullback is the degreewise simplicial pullback.
- The opposite enriched base A is the domain
  `(PinchedCube.rigidification.obj K)ᵒᵖ` of `represented.functor`,
  `singularRepresented.functor`, and the existing straightening functor.
- R(k) is `representedValue v c (Straightening.vertex k)`, namely the rigidification
  Hom from the image of k under rigidification of v to `Pinched.vertex C c`.
  `representedAction` is explicitly rigidification of v on Hom, tensor the identity,
  followed by enriched composition. `represented` packages precisely this action as
  an enriched presheaf. No Kan replacement is used for R.
- The tautological cone epsilon is `evaluation v c`. `displayedCone` extracts the
  stored slice extension from the second pullback projection. `evaluation_unique`
  prescribes epsilon on the pure final block and on the entire cone of EVERY simplex
  of E. It is an existence-and-UNIQUENESS universal property. These maps include the
  pure initial block and every repeated-final-vertex simplex, even when E is empty.
  A slice extension is a simplicial map out of `Delta[n] star Delta[0]`: evaluation
  on a mixed block with several final vertices therefore uses the standard collapse
  of that final block, precisely the node's formula, not a different cone convention.
- The initial restriction is `evaluation_base`. `pushoutEvaluation` is the actual
  `pushout.desc` of rigidification of evaluation and of v. Its object images are
  `pushoutEvaluation_base` and `pushoutEvaluation_vertex`; `counit` applies its actual
  enriched Hom map and only transports those prescribed endpoints.
- The first main conjunct states the full uncurried enriched naturality equation
  using the dependency's `ConePresheaf.action` on BOTH sides. It quantifies over all
  objects of rigidification, hence all mapping simplices, not only ordinary arrows.
  `counitTransformation` is the actual shared `ConePresheaf.homMk`, with these maps
  as its components, from `(ConePresheaf.left K).obj (Over.mk q)` to `represented`.
- The component weak-equivalence assertion is
  `Enhanced.IsWeakHomotopyEquivalence (counit v c (Straightening.vertex k))` for EVERY
  vertex k. This is the dependency's realization/path-component/based-homotopy-group
  predicate, without changing the meaning to a categorical equivalence.
- E_k is the existing `Enhanced.fiber q k`. The uniquely specified
  `fiberIdentification v c k` is an isomorphism to
  `Enhanced.mappingSpace C (v.app _ k) c`; the `IsIso` assertion is in the main theorem.
  Its defining formula projects to the slice and evaluates on `joinPointTopSimplex`.
  Thus the fiber identification is the recorded right-pinched one in every degree.
- The canonical fiber-inclusion map is `fiberInclusion q k` with source
  `Pinched.realization.obj (Enhanced.fiber q k)` and target `Straightening.value q k`.
  Its existence-and-uniqueness universal property specifies it after every
  `resolutionGenerator n` and every coend summand. `fiberGenerator` is the ACTUAL map
  of the cone of the fiber simplex into the enriched pushout, with prescribed endpoint
  transports. Consequently this is the inclusion-induced map, not a map selected
  from the assertion that some weak equivalence exists. Over a point the enriched
  pushout is rigidification of J^n; its mapping map is `resolutionGenerator`, so these
  are exactly the published fiberComparison generators after Q-realization.
  The main theorem explicitly states that this canonical inclusion is weak.
- `vertexCounit` makes the canonical rigidification vertex-naturality transport
  explicit, so the main composite identity is an ORDINARY equality of simplicial maps:
  `fiberInclusion q k ≫ vertexCounit v c k =
  Pinched.realization.map (fiberIdentification v c k) ≫
  Pinched.comparison C (v.app _ k) c`.
  Its source transport is the specified fiber identification, not a homotopy or an
  uncharacterized equivalence of spaces.
- The final main clause is the equality on EVERY Q^n summand, written with
  `Pinched.summand` on the left and the existing `Pinched.comparisonSummand` on the
  right. The latter is, by its actual definition, rigidification of
  `Pinched.simplexToMap`, i.e. precisely the map J^n to C supplied by the simplex e.
- Naturality in C,K,c,v is `slice_straightening_counit_naturality`. Its inputs are any
  simplicial maps f:C to D and g:K to L, a square `v ≫ f = g ≫ w`, and the matching
  pointed equality `f(c)=d`. `totalMap_unique` supplies the unique induced pullback-slice
  map by its base projection and every displayed cone; `totalMap` is that map. The
  theorem gives the evaluation square, the counit square, the singular-unit square,
  the fiber-inclusion square and the mapping-fiber identification square. The few
  `HEq`s in THIS theorem account only for the equal endpoints f(v(k))=w(g(k)) and
  f(c)=d. They express strict equality after endpoint transport, not a homotopy.
- The last naturality clause quantifies over EVERY `a : n ⟶ m` in SimplexCategory
  and every fiber simplex e. It is the coend relation for inclusion on those summands,
  so it includes all faces, degeneracies, their repetitions and their composites.
  Together with the main summand formula, it is the requested compatibility for psi i.
- H(k) is `Spaces.singularRealization.obj (representedValue v c ...)`, literally
  `Sing |R(k)|`. Its enriched action is `singularAction`, using the existing
  `Spaces.topEnrichment` and the realization/singular units before composition.
  `singularRepresented` packages this action. `singularCounit` is exactly counit
  followed by `sSetTopAdj.unit.app`, and `singularCounitTransformation` packages it
  as the actual enriched transformation. The second main conjunct gives enriched
  naturality and the vertex clauses state its weak equivalence and the Kan property
  of its target. No Kan hypothesis on R(k) is assumed.

### Construction obligations and dependencies

The auxiliary existence theorems are UNIQUE universal properties, not mere existence
of objects. `evaluation_unique` determines its map on a jointly generating family of
simplex cones and the pure final block. `fiberInclusion_unique` determines its map on
all coend summands after the quotient generators; those generators are degreewise
surjective. `fiberIdentification_unique` determines the image of every simplex.
`totalMap_unique` determines the base projection and every slice extension.
Using their `.exists.choose` constructs an object determined up to the actual equality
used downstream, exactly the universal-property case allowed by AGENTS.md section 5.
No choice is taken from a bare `Nonempty`, an unspecified equivalence, or a weak-map
existence proposition. Each postponed well-definedness, endpoint, uniqueness or
functor-law theorem has the owning node's blueprint tag and its full mathematical
proof in its docstring. All are construction obligations of this same notion; there
are no independent new notions or changed dependency interfaces.

I read the dependency statements, their recorded Lean records, the recorded main
signatures/docstrings, and the actual constructions used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.mappingSpace`, `mappingSpaceMap`, `IsWeakHomotopyEquivalence`.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`:
  `SSet.Enhanced.joinSlice`, `joinSliceProjection`, `JoinSliceSimplex`,
  `joinPointTopSimplex`, and `joinSlice_right_fibration`.
- `Sheaf.CategoryTheory.SimplicialRightFibrationPresentation`:
  `SSet.SimplicialRightFibration.Diagram`, `Presentation`, and
  `simplicial_right_fibration_presentation`; the presented cone functor is the existing
  `SSet.ConePresheaf.left`. Its actual implementation in
  `Sheaf.AlgebraicTopology.ConePresheafAdjunction` uses
  `SSet.Straightening.straightening`; its shared full-enriched `homMk` and `action`
  are reused here. No model structure or replacement is selected from Presentation.
- `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison`:
  `SSet.Straightening.coneMap`, `simplexInclusion`, `vertex`, `conePushout`,
  `baseInclusion`, `coneInclusion`, `coneVertex`, `value`, `valueAt`, `valueMap`,
  `fiberMap`, `fiberComparison`, `precomposition`, and
  `right_straightening_fiber_comparison`. Only its existing construction data is used
  to define the counit and inclusion; the comparison theorem is the node's proof plan.
- `Sheaf.CategoryTheory.PinchedRigidificationResolution`:
  `SSet.Pinched.coherentSimplex`, `rigidification`, `coherentSimplexInclusion`,
  `vertex`, `vertex_naturality`, `simplex`, `quotient`, `initial`, `terminal`,
  `resolution`, `realization`, `summand`, `mappingMap`, `comparisonSummand`,
  `comparison`, and `pinched_rigidification_resolution`.
  The Pinched and PinchedCube rigidification presentations used by the dependencies
  are definitionally compatible; no private rigidification or universe restriction
  was introduced to bridge them.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.singularRealization`, `topEnrichment`, `topUnit_laws`,
  `singular_kan` and the source's enriched representable construction. The node here
  is the contravariant representable, whereas the recorded `corepresented` fixes
  its FIRST variable; it is therefore not mistakenly reused in the wrong variance.
- Proof-only `Sheaf.AlgebraicTopology.RealizationSingularUnitWeak`:
  `SSet.Enhanced.realization_singular_unit_weak` for the exact unit composed here.

### Edge cases checked before and during writing

K may be empty. Then E is empty and its cone still has its pure final vertex;
`evaluation_unique` explicitly fixes this block, while all vertex conclusions are
vacuous. Fibers and mapping spaces may be empty, for example in a discrete C with
v(k) different from c: Q-realization and straightening both have the empty mapping
value, and the weak-equivalence predicate needs no basepoint. For C=K=Delta[0] and
v=id, Q^0 is the point and the summand formula is evaluation of the identity edge.
Equal endpoints, identity edges and degenerate simplices are not excluded. At n=0
`first` and `last` lie in the coherent interval and the pinched quotient is the
specified J^0. Mixed simplices with multiple final vertices are maps of the whole
join, so their collapse rule is forced by simpliciality. All monotone ordinal maps
are quantified, with no injectivity condition that would omit degeneracies.
The comparison is checked in maps of simplicial sets, with no loss to pi_0.

I read Lurie's HTT at the source URL, including pp. 76, 87 and 88 (the PDF's page
numbers differ): the Q-realization identification over a point, Proposition the project server,
and Proposition the project server and its factorization through slice straightening. The node is
an extracted natural pullback version of that construction, not a claimed verbatim
HTT assertion. No source-based statement correction was needed.

### Searches

Actual searches were run through `msearch.py N9 lem-coef-slice-straightening-counit`:

- LeanFinder: “The tautological right slice cone compares straightening with the
  simplicial enriched representable mapping presheaf”. Eight hits concerned ordinary
  enriched functor-category cones, ordinary Kan extensions and strict Segal Kan
  extensions; none gives this slice/pinched comparison.
- Loogle: `"straightening"`. Zero hits.
- Mathlib grep, CategoryTheory: `straighten|pinched|tautological.*cone`. Thirteen hits
  concern ordinary tautological presheaf cocones and their colimit proofs. I inspected
  `Presheaf.isColimitTautologicalCocone`; it is the ordinary presheaf decomposition,
  not this coherent right-slice comparison. It underlies the general simplex-colimit
  construction already supplied by the dependencies.
- LeanSearch: “The tautological cone of the right slice compares simplicial
  straightening with the enriched representable by a weak homotopy equivalence”.
  Eight hits concerned that same ordinary cocone, ordinary Kan extensions, homotopy
  category units, representable simplices and simplicial enrichment Hom bijections.
  None is this theorem or a one-line specialization.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` trees for
  `sliceStraightening|SliceStraightening|slice_straightening_counit|tautological.*slice`
  found only descriptive text in `CoherentDiagramCoyoneda`, not a declaration.
  The exact node-id upstream search also found no occurrence. Broader conceptual
  search located the existing straightening fiber comparison and pinched-resolution
  modules, which were read and reused, not duplicated.

There is no exact existing statement to bind with `existing: true`. No new nodes,
no dependency modules, no `statement_change`, and no STATEMENT-DISPUTED claim are needed.

### Verification

The prescribed single-file `scompile.py` wrapper compiled this module both as sandbox
and as the library-path copy against the side-project overlay. The latest completed
run before this report took 16.4 seconds and 7.4 seconds, both below the unchanged
60-second limit, with no errors or warnings. Every universe and variable is explicitly
bound, `autoImplicit` is false, and every line is at most 100 characters. The delivery
wrapper will repeat compilation and run the server's preflight before any push.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
