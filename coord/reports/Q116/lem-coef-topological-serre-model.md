## Worker report

The module `Sheaf.AlgebraicTopology.TopologicalSerreModel` states the Serre model
structure on `CompactlyGenerated.{u, u}`. The sole postponed theorem is
`CompactlyGenerated.Serre.topological_serre_model`, with proof `sorry`. All helper
definitions have real data and make only the generator maps and morphism classes
introduced by this node. No new nodes or dependency replacements were necessary.
The three k-space instances are existing Mathlib instances exposed through the
bundled disk definitions with `inferInstanceAs`; they assert no new postponed results.
No statement correction or disputed statement was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The category K is `CompactlyGenerated.{u, u}`, the exact category of
  `SSet.realization_finite_limits`. It imposes no Hausdorffness or weak Hausdorffness
  on arbitrary spaces. Its small limits and colimits are the dependency's assertions.
- Continuous maps are the morphisms in this category, via its fully faithful
  `compactlyGeneratedToTop` functor. There are no restrictions on source or target.
- W is `Serre.W`: `Function.Bijective (SSet.Enhanced.componentsMap ...)` is the
  path-component bijection, and `∀ r, 1 ≤ r → ∀ x : X, Function.Bijective
  (SSet.Enhanced.homotopyGroupMap ... r x)` gives all positive based homotopy-group
  isomorphisms at every source basepoint. These are the recorded dependency's actual
  cubical postcomposition maps; they preserve concatenation, so bijection is exactly
  group isomorphism, including the noncommutative fundamental group.
- `boundaryInclusion n` lifts `TopCat.diskBoundaryInclusion n` unchanged from TopCat
  to K. `TopCat.disk n` is the closed unit ball in `EuclideanSpace ℝ (Fin n)`, with
  Mathlib's canonical `ULift` for universe u. `TopCat.diskBoundary n` is its unit
  sphere with the subspace topology. Thus it is S^(n-1), and its dimension-zero
  instance is the empty S^(-1). `I = MorphismProperty.ofHoms boundaryInclusion`.
- `cylinderBottom n` is the continuous function `x ↦ (x, 0)` from the very same disk
  to its ordinary product with `unitInterval`. Its source is canonically D^n × {0}.
  `J = MorphismProperty.ofHoms cylinderBottom`. The dimension index is all `ℕ`.
- F is definitionally `J.rlp`: the right lifting class of exactly those disk-cylinder
  inclusions. Mathlib's `rlp` requires a diagonal filler in every commutative square.
- C is definitionally `(F ⊓ W).llp`, precisely the specified left lifting class.
- `W.IsStableUnderRetracts` gives retract closure in the arrow category, and
  `W.HasTwoOutOfThreeProperty` gives all three cases of two-out-of-three.
- `IsWeakFactorizationSystem C (F ⊓ W)` and
  `IsWeakFactorizationSystem (C ⊓ W) F` each assert factorization of every map,
  L = R.llp and R = L.rlp; see the Mathlib class's full signature and docstring.
  This is the node's explicit definition of the model axioms. The existing limits
  and colimits come from the statement dependency, rather than a redundant hypothesis.
- Both `HasFunctorialFactorization` conjuncts assert the specified functorial choices.
  Its data consist of a functor `Z : Arrow K ⥤ K` and natural transformations
  from the source and to the target, whose composite is the original arrow. Thus
  functoriality is in arbitrary commutative squares, not only individual objects.
- `I.rlp = F ⊓ W` identifies I as generating cofibrations. F = J.rlp is definitional,
  and the second weak factorization system identifies J as generating trivial
  cofibrations. Thus both generating sets are the actual prescribed maps.
- `J ≤ C ⊓ W` includes every generating trivial cofibration. The final four
  conjuncts give closure of C ∩ W under pushouts (`IsStableUnderCobaseChange`),
  u-small coproducts (`IsStableUnderCoproducts.{u}`), u-small transfinite composites
  continuous at limit stages (`IsStableUnderTransfiniteComposition.{u}`), and
  arrow retracts (`IsStableUnderRetracts`). These assert closure for the whole
  trivial-cofibration class, so cover all the iterated operations in the node.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicTopology.RealizationFiniteLimits`,
  `SSet.realization_finite_limits`: exact k-space category and all small limits and
  colimits; the module and full theorem docstring/signature were read.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.componentsMap`, `SSet.Enhanced.homotopyGroupMap`: their full
  definitions and docstrings were read. The module is available through the public
  import of the realization dependency, which already publicly imports it.
- Stated proof dependencies imported without `public`:
  `Sheaf.Topology.CompactClosedT1Chain` (`TopCat.compact_closedT1_chain_factorization`),
  `Mathlib.Topology.CompactOpen` (`ContinuousMap.curry`, `ContinuousMap.uncurry`),
  `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument`
  (`CategoryTheory.SmallObject.functorialFactorizationData`). Their relevant
  signatures/docstrings were read. The exact-sequence and sphere-mapping proof
  dependencies have no Lean record yet, so have no module to import. The theorem's
  nine-step proof docstring preserves their uses for stage 3.
- Mathlib's disk, boundary, and inclusion in `Topology.Category.TopCat.Sphere`,
  its `CompactlyGenerated` category, `MorphismProperty.ofHoms`, `llp`, `rlp`,
  `IsWeakFactorizationSystem`, `HasFunctorialFactorization`, and the four closure
  classes are reused. There is no independent copy of these notions.

Edge cases checked before and after writing:

- Dimension zero: the Euclidean vector space has a single zero vector. Its unit
  closed ball is a point; its unit sphere is empty. I therefore includes the empty
  boundary-to-point map and J includes the initial endpoint-to-interval map.
- Empty arbitrary spaces are allowed. The based-group clause is vacuous for empty
  sources, while path-component bijectivity still prevents an empty-to-nonempty
  map from being a weak equivalence. No global inhabitedness is assumed.
- Every positive degree and every source basepoint is quantified. No connectedness
  or basepoint-surjectivity hypothesis is inserted, and degree one is included.
- The empty coproduct is included by `IsStableUnderCoproducts.{u}`. The transfinite
  class uses well-order-continuous diagrams and their colimit cocones, so limit
  topology/continuity is retained, not an arbitrary discontinuous chain.
- The single universe u is the dependency's object-size and hom-size convention,
  not an extra equality imposed on an independent site. Mathlib's disk `ULift`s
  realize the generators in every such universe, including u = 0.

Searches (2026-10-16 UTC):

- `msearch.py ... leansearch "Serre model structure on compactly generated topological
  spaces"`: 8 hits, including `CompactlyGenerated`, its constructor, the general
  `ModelCategory` class and simplicial-set model data; no topological Serre theorem.
- `msearch.py ... leanfinder "The Serre model structure on compactly generated
  topological spaces with weak homotopy equivalences and Serre fibrations"`: 8 hits,
  generic model-category constructors, delta-generated spaces, and simplicial-set
  fibrations/cofibrations; no matching Serre model statement.
- `msearch.py ... loogle "TopCat, ModelCategory"`: 0 hits, with service diagnostic
  `unknown identifier 'ModelCategory'`. Direct Mathlib source searches independently
  located the general `HomotopicalAlgebra.ModelCategory` definition.
- `msearch.py ... grep "Serre|serre|IsWeakHomotopyEquivalence"`: mostly unrelated Serre
  number-theory and abelian-category hits, no topological Serre structure. Focused
  direct `rg` in Mathlib's Topology and AlgebraicTopology confirmed no exact theorem.
- Direct `rg` for disk, sphere, cylinder and boundary maps found and inspected
  `Mathlib/Topology/Category/TopCat/Sphere.lean`; its exact objects/maps are used.
- Direct `rg` in `WeilConjectures/` and `lean/Sheaf/` for Serre and weak homotopy/model
  names found no topological Serre structure. Existing project Kan–Quillen statements
  concern SSet, hence do not state this node. Their statements were inspected.
- `grep -rn "lem-coef-topological-serre-model" WeilConjectures/` and `rg` for that id
  in `dag/lean_names_upstream.json` returned no match. The chosen full declaration
  names were checked against the named source directories; no duplicate was found.
- Opened the node's Hovey PDF URL and checked Definition 2.4.3, Theorem 2.4.19,
  and Theorem 2.4.23: these use the same disk sets and k-space restriction. No
  unit statement is changed. URL: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf

Validation: `scompile.py Q116 lem-coef-topological-serre-model` compiled this module
cleanly as both a sandbox file and its final library module (2.7 s and 2.9 s).
The first diagnostic was only missing synthesis through the opaque bundled disk
objects; exposing existing Mathlib k-space instances repaired this with real data.
Every Lean line has at most 100 characters. All universes and variables are bound;
`autoImplicit` is disabled. Independent second reading is assigned after this worker.

## Second reading by Q116

Independent second reader, 2026-10-17. I opened the sandbox node and module,
both statement-dependency nodes and their source declarations, the recorded proof
dependency declarations, and Hovey's cited PDF. This is a statement-stage review;
the item remains a named theorem with `sorry`. Verdict: the Lean says what the
node says. No mathematical or interface mismatch was found, so no Lean or node
change was needed. This section is the only editorial change of this reading.
There are no new definition nodes, dependency replacements, repair note, or
`statement_change` to review or audit through citers.

Here is my object/hypothesis/conclusion inventory, matched in the node's order.
Names below are in `CompactlyGenerated.Serre` unless qualified.

1. The category K and continuous maps: `CompactlyGenerated.{u, u}`, with
   `compactlyGeneratedToTop.map f` its actual continuous map. I read
   `SSet.realization_finite_limits`, including its `HasLimits`, `HasColimits`,
   and topological-colimit conjuncts, and Mathlib's category and fully faithful
   inclusion definitions. These give exactly the dependency's full category of
   k-spaces. No weak Hausdorff, Hausdorff, inhabitedness, or connectedness
   assumption occurs. PASS.
2. Path components: the first conjunct in `W` is
   `Function.Bijective (SSet.Enhanced.componentsMap ... .hom)`. That dependency
   declaration is a quotient map on `ZerothHomotopy`, using mapped paths, so it
   is path components rather than connected components. PASS.
3. All based homotopy groups: the second conjunct of `W` is
   `∀ (r : ℕ), 1 ≤ r → ∀ (x : X), Function.Bijective
   (SSet.Enhanced.homotopyGroupMap ... .hom r x)`. I read that definition: it
   postcomposes actual cubes into X and their homotopies relative to the entire
   boundary. Mathlib's `HomotopyGroup (Fin r)` is exactly this quotient. The
   induced maps preserve concatenation, so their bijectivity means group
   isomorphism in every positive degree, including nonabelian degree one.
   The quantifiers include every source basepoint, as the dependency specifies.
   No simplicial-set weak-equivalence predicate is incorrectly applied to K.
   PASS.
4. Disks, spheres, and dimensions: `boundaryInclusion (n : ℕ)` uses the actual
   `TopCat.diskBoundaryInclusion n`. I read `TopCat.disk` and `diskBoundary`:
   these are the ULift of the closed unit ball and unit sphere in
   `EuclideanSpace ℝ (Fin n)`. The boundary has the subspace topology.
   `I = MorphismProperty.ofHoms boundaryInclusion` therefore lists precisely
   all the required boundary inclusions. PASS.
5. Cylinder inclusions and Serre fibrations: `cylinderBottom n` is the map
   `x ↦ (x, 0)` into the ordinary product `TopCat.disk n × unitInterval`.
   This identifies its source with the cylinder bottom, with no changed
   topology. `J = .ofHoms cylinderBottom`, and `F = J.rlp`. I read Mathlib's
   `rlp`: it demands `HasLiftingProperty` against every member, hence all
   commutative squares for every specified dimension. PASS.
6. Cofibrations: `C = (F ⊓ W).llp`. Mathlib's `llp` quantifies over all arrows
   in its right class, not a subset of them. This is the specified
   left orthogonal of the Serre weak equivalences. PASS.
7. Retracts and two-out-of-three for W: the first two theorem conjuncts are
   `W.IsStableUnderRetracts` and `W.HasTwoOutOfThreeProperty`. I read the class
   fields: the former uses `RetractArrow`, and the latter includes composition
   and both cancellation cases. All the node's cases are asserted. PASS.
8. First weak factorization system: `IsWeakFactorizationSystem C (F ⊓ W)`.
   The Mathlib class has `rlp`, `llp`, and `hasFactorization` fields, giving
   both orthogonal-class equalities and a factorization of every arrow, in
   exactly the specified left-then-right order. PASS.
9. Second weak factorization system:
   `IsWeakFactorizationSystem (C ⊓ W) F`, using the same full class. PASS.
10. Functoriality of both factorizations: the two `HasFunctorialFactorization`
    conjuncts use the same ordered pairs as items 8 and 9. I read
    `FunctorialFactorizationData`: its intermediate-object functor has domain
    `Arrow K`, and its two legs are natural transformations satisfying the
    factorization equation and the class-membership fields. This is
    functoriality in arbitrary commutative squares. PASS.
11. Generating cofibrations: `I.rlp = F ⊓ W`, together with item 8 and the
    specified I, says exactly that these boundary inclusions generate the
    first system. No arbitrary generating set is substituted. PASS.
12. Generating trivial cofibrations: `F = J.rlp` is the actual definition,
    and item 9 identifies its left class with `C ⊓ W`; `J ≤ C ⊓ W` explicitly
    includes every cylinder generator. Thus this generating-set assertion
    is present even without a redundant separate equality for J. PASS.
13. All the final operations: the last four conjuncts assert that `C ⊓ W`
    is stable under cobase change, `IsStableUnderCoproducts.{u}`,
    `IsStableUnderTransfiniteComposition.{u}`, and arrow retracts. I read
    their fields. Cobase change uses arbitrary pushout squares; coproducts
    quantify over every `J : Type u`; transfinite composition uses a
    well-order-continuous functor with an actual colimit cocone, via
    `CategoryTheory.TransfiniteCompositionOfShape`. These cover all the
    stated iterated operations on J. Closure of the whole left lifting
    class follows already from item 9, so this formulation adds no
    independent stronger mathematical requirement. PASS.

Source check: Hovey, Definition 2.4.3 (printed pp. 50-51) gives the same
boundary and cylinder maps and the same based homotopy tests. Definition
2.4.21 and Proposition 2.4.22 (printed pp. 57-58) distinguish K from the
weak Hausdorff subcategory T. Theorem 2.4.23 and its proof (printed pp. 58-59)
use K and these same generating sets, inheriting the model structure of
Theorem 2.4.19. I checked these places directly in
[the cited PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf).
This node has no Stacks source place; no extra standing hypothesis is needed.
The theorem does not claim the additional Quillen-equivalence conclusions
that are in Hovey but absent from this DAG node.

Edge cases: n = 0 gives a singleton closed ball and an empty unit sphere
because the unique vector has norm zero. Thus I contains the empty-to-point
map, and J contains the initial endpoint-to-interval map. Empty source and
target spaces are allowed. The based-group clause is vacuous for an empty
source, but the independent component bijection still rejects an
empty-to-nonempty weak equivalence. No basepoint is globally chosen.
Degree zero is covered by path components and degree one by the positive
group clause. The empty coproduct is included. A transfinite composite is
required to be continuous at limits; finite chains and identity cases are
allowed too. There is no ring, characteristic, scheme, or coefficient n in
this node. The arbitrary universe u, including u = 0, is exactly the
recorded k-space size convention; ULift places every disk in that universe.
There is no extra site-universe equality or smallness hypothesis on objects.

Independent searches, with different formulations from the worker's:

- LeanSearch through `msearch.py`: "Serre fibrations and weak homotopy
  equivalences form a model structure on topological spaces" returned eight
  generic model-category and simplicial-set results. None states the
  topological theorem.
- LeanFinder through `msearch.py`: "disk inclusions generate a cofibrantly
  generated model category of k spaces with Serre fibrations" returned eight
  generic model-category and simplicial-set results, with no topological
  Serre model structure.
- Loogle through `msearch.py`: `CompactlyGenerated` returned twelve hits for
  the existing category, constructors, inclusion, and full/faithful data.
  I opened the source and confirmed that these notions are reused.
- Direct `rg` in Mathlib's Topology/AlgebraicTopology, upstream
  `WeilConjectures`, and project `lean/Sheaf` for
  `serre.?fibration|serre.?model|weak.?homotopy.?equivalence|cylinderBottom`
  found the enhanced simplicial convention and its consumers, but no
  existing theorem on topological k-spaces. The separate search for
  `diskBoundaryInclusion` found Mathlib's canonical map, already reused.
  The project `KanQuillenRightProper` statement is about simplicial sets,
  not this node. The enhanced `IsWeakHomotopyEquivalence` likewise takes
  simplicial maps, so it is not a duplicate of W on K. The chosen names
  are absent from `dag/lean_names_upstream.json`.

H5/H6/H8/H9 check: each helper has actual data; the three k-space instances
expose existing Mathlib instances through the bundled disk definitions.
They are neither postponed assertions nor new notions. The only theorem
is `topological_serre_model`, whose whole proof is `sorry`. Its docstring
tracks all nine DAG proof steps, including change of basepoint, compact
chains, the Q comparison, the retract argument, and restriction to K.
Every declaration has its source and blueprint tag. The imports for the
recorded compact-chain, currying, and small-object proof dependencies are
present; the two remaining proof dependencies still have no Lean record.
No local notation, private copies, unbound variables, hidden hypotheses,
or line over 100 characters was found. I checked the literal main
signature against `lean.statement`; they agree verbatim.

Validation: reran `scompile.py Q116 lem-coef-topological-serre-model` with
the sandbox module's full path. Both the sandbox and final library module
compiled cleanly, with no diagnostics (1.6 s and 1.7 s respectively).
