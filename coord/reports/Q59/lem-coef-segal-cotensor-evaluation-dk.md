## Worker report

The module `Sheaf.AlgebraicTopology.SegalCotensorEvaluationDK` states
`SSet.SegalSpace.cotensor_evaluation_dk`, Rezk Lemma 13.9, with its complete eight-step
DAG proof in the declaration docstring. The theorem is postponed with `sorry`; the
three definitions have real data and no postponed data or choice from an existence theorem.
The node statement and dependency lists are unchanged. There is no statement dispute.

### Hypotheses and clauses

- Small simplicial sets and simplicial spaces: the explicit `universe u` and
  `W : SSet.SegalSpace.SimplicialSpace.{u}` quantify over every small size. This is
  `SimplexCategoryᵒᵖ ⥤ SSet.{u}`; both simplicial directions and all their operators are
  retained. There are no auto-bound implicit variables.
- The sole mathematical hypothesis, that W is a Segal space, is `hW : IsSegal W`.
  This is the dependency's exact predicate: Reedy fibrancy using the opposite-injection
  matching maps, and realization weak equivalences of the consecutive-edge maps for
  every `n : ℕ` with `2 ≤ n`. It does not assume completeness, connectedness, or existence
  of vertices.
- The Kan model and Reedy conventions are inherited through the recorded
  `SegalCartesianExponent` module. Its `IsReedyFibration` uses the recorded
  `HomotopicalAlgebra.Reedy.rightClass`; its `IsSegal` uses the recorded
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, which means bijection on realization path
  components and bijection on all positive based homotopy groups.
- The strict mapping space is the existing `SSet.Segal.mappingFiber`. Its subcomplex
  imposes the two actual endpoint equations `(d₁,d₀)=(x,y)` in every inner degree,
  with constant degeneracies of x and y. `SSet.Segal.mappingFiberMap` is the actual
  induced map, not a freely supplied comparison.
- The existing `SSet.Segal.homotopyCategory` is Mathlib's edge-path/triangle-relation
  category of the outer simplicial set of inner vertices. Its objects are precisely
  the vertices of W₀. Degeneracies give identities and degree-two triangle relations
  give composition. The existing `homotopyCategory_homs` declaration in its owning
  module identifies these hom sets with π₀ of the strict mapping fibers for Segal
  spaces. It is reused, not restated here.
- `IsDwyerKanEquivalence t` renders the node's definition literally:
  `(SSet.Segal.homotopyFunctor t).IsEquivalence` and, for every pair x,y of original
  vertices, `Enhanced.IsWeakHomotopyEquivalence (SSet.Segal.mappingFiberMap t x y)`.
  The predicate is applied only between the Segal spaces asserted in the theorem.
  There is no replacement of categorical equivalence by a bare object bijection.
- The outer representables and constant inner spaces are the dependency's
  `discreteRepresentable` and `constant`. The exponential is exactly Mathlib's
  `ihom` with the dependency's `instMonoidalClosed`, hence its bidegree simplices are
  maps `A × F(n) × cΔ[q] → W` with precomposition operators. No exponential is redefined.
- The walking groupoid is the existing `SSet.Segal.WalkingIso`, the codiscrete category
  on `ULift Bool`, with exactly two objects and a unique arrow per ordered pair.
  `SSet.Segal.E` is its nerve, discrete in the inner direction. The existing
  `SSet.Segal.endpoint i : F 0 ⟶ E` selects false=0 or true=1.
- `cotensorConstant W` is `MonoidalClosed.curry (snd E W)`: a generalized simplex
  w becomes the E-indexed constant diagram w. This is the canonical restriction
  along E→F(0) under W^F(0)≅W.
- `cotensorEvaluation W i` pairs the constant map to the specified endpoint of E
  (using `toFZero` and `endpoint i`) with the identity of W^E, then applies
  `(ihom.ev E).app W`. It is the canonical restriction along e_i followed by the
  same W^F(0)≅W identification. The product order is E × W^E, as required by ihom.
- The first conclusion `IsSegal ((ihom SSet.Segal.E).obj W)` asserts the stated Segal
  property of W^E. The second is DK equivalence of j. The final `∀ i : Bool` asserts
  DK equivalence of each of p₀,p₁, with no endpoint excluded.

### Dependencies and import direction

Recorded statement-dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` (and the recorded main declaration
  `SSet.Enhanced.coneCategory`, read with its docstring). The realization-based weak
  equivalence is what occurs in both the Segal and DK predicates.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` and its fixed Kan model structures.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.model_structure`, `rightClass`, `relativeMatching`.
- `Sheaf.AlgebraicTopology.SegalCartesianExponent`:
  `SSet.SegalSpace.SimplicialSpace`, `instMonoidalClosed`, `IsSegal`, and
  `cartesian_exponent`. This module publicly imports the other three dependencies.

A supplemental public import of the already landed
`Sheaf.AlgebraicTopology.SegalCategoricalEquivalence` reuses its explicit definitions
`SSet.Segal.mappingFiber`, `mappingFiberMap`, `homotopyCategory`, `homotopyFunctor`,
`WalkingIso`, `E`, `endpoint`, and `toFZero`. This avoids second definitions of notions
which both nodes introduce in their introductory conventions. No assertion of that
module, particularly `categorical_equivalence_dk`, is used to prove this item. That
node already has the current item as a proof dependency, so adding it to this item's
DAG dependencies would create a cycle. No such edge is added. For the same reason,
the eventual reverse proof import of this module into `SegalCategoricalEquivalence`
must be omitted under stages/2-statements §3(7); its definitions can be moved to a
shared upstream module later without changing this statement. This report records
the import-cycle omission rather than copying those definitions.

The two other currently stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicTopology.KanFibrationArbitraryBaseFibers`
(`SSet.weakEquivalence_iff_strictFiberwise`) and
`Sheaf.AlgebraicTopology.ContractibleHomotopyFiberEquivalence`
(`SSet.Enhanced.isWeakHomotopyEquivalence_iff_contractible_homotopyFiber`).
The DK two-out-of-six and equivalence-classifier nodes have no Lean records in the
read snapshot, so their imports are left for the maintainer when they are stated.

### Edge cases and source

Empty W has no vertices and empty mapping fibers; the universal mapping-fiber
condition remains vacuous while the category-equivalence condition is still present.
There is no `Nonempty` binder. Empty fibers between particular vertices are included
in the universal x,y quantifier. Both Bool endpoints are covered, and arbitrary u
includes large choices of small sets after enlargement. The definition of Segal imposes
no spurious condition at n=0 or n=1. In particular a discrete nerve of a category with
nonidentity isomorphisms, which need not be complete as a Segal space, is not excluded.

Read the cited PDF online, Lemma 13.9 (printed pp.31–32), together with its neighboring
Proposition 13.8 and the referenced conventions. The source states precisely the
three DK equivalences for a Segal space. The DAG's expanded proof is copied step by
step into the docstring, including the empty-fiber cancellation and the argument for
homotopy-category equivalence independent of Proposition 13.8. No correction is needed.

### Searches

- `msearch.py ... leanfinder`: “For a Segal space the constant map to the walking
  isomorphism cotensor and its evaluation maps are Dwyer Kan equivalences”: eight
  hits, including product-simplex nerves, strict Segal nerves and nerve/homotopy-category
  comparisons; none states this theorem.
- `msearch.py ... loogle`: `"Segal", "Dwyer"`: zero hits.
- `msearch.py ... leansearch`: “Evaluation from a Segal space exponential by the walking
  isomorphism is a Dwyer Kan equivalence”: eight hits about ordinary walking diagrams,
  whiskering, and Dold–Kan; no Segal-space cotensor theorem.
- `msearch.py ... grep` in Mathlib/AlgebraicTopology:
  `SegalSpace|cotensor.*evaluation|DwyerKan`: zero hits.
- `rg` in the source repository for the item id and
  `cotensor.*evaluation|SegalSpace|DwyerKan`: zero hits. This also performed the requested
  exact-item attachment search.
- `rg` in `lean/Sheaf` for Segal/DK, mappingFiber, homotopyFunctor and walking-isomorphism
  names found `SegalCartesianExponent` and `SegalCategoricalEquivalence`. Read the complete
  relevant definitions and docstrings; reuse these. The latter's theorem assumes
  specified categorical homotopy inverses, whereas this node supplies the three
  canonical maps and proves their DK properties, so it is not an existing match.
- Exact-name `rg` across Mathlib, the source repository, `dag/lean_names_upstream.json`,
  and `lean/Sheaf` found no existing `IsDwyerKanEquivalence`, `cotensorConstant`,
  `cotensorEvaluation`, or `cotensor_evaluation_dk` declaration.
- No repair note exists at the item path. No new node or dependency repair is needed.

### Validation

On 2026-10-17, `scompile.py Q59 lem-coef-segal-cotensor-evaluation-dk` compiled this
delivered module separately through its prescribed overlay: exit 0, no errors and no
warnings; sandbox and library-path checks each took 1.3 s.
Every line is at most 100 characters. Every universe and binder is explicit.
`deliver2.py Q59 lem-coef-segal-cotensor-evaluation-dk --no-push` printed
`OK (dry run)`: the commit compiles and passes preflight except for the independent
second reading, as expressly permitted by the worker dry-run wrapper. Nothing was pushed.
The dry run is repeated after updating this report and the UTC record date. The independent second reader writes their own section
and delivers; no second-reading section is authored by this worker.

## Second reading by Q59

Independent second reader, 2026-10-17. I opened the sandbox node and complete Lean
module, the four statement-dependency records and their source declarations, and
`SegalCategoricalEquivalence.lean`, including its helper theorem and final signature.
I read the archived Rezk PDF and checked the online source named by the node:
<https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf>.
The applicable places are Sections 2.3--2.4, Definition 4.1, Sections 5.1--5.5 and
7.4, Corollary 7.3, Section 13.1, and Lemma 13.9 on printed pages 31--32.
This node has no Stacks source. The source assumes a Segal space here, with no
completeness, nonemptiness, connectedness, or finiteness hypothesis.

### Object, hypothesis, and conclusion audit

1. Small simplicial sets and weak homotopy equivalences: `SSet.{u}` and the reused
   `SSet.Enhanced.IsWeakHomotopyEquivalence` have the node's meanings. I read its
   realization-component bijection and positive based homotopy-group bijections.
   The recorded Kan-model theorem fixes these weak equivalences and the horn-lifting
   fibrations; no extra model structure is supplied as a hypothesis here. Verdict: exact.
2. A simplicial space: `SSet.SegalSpace.SimplicialSpace.{u}` unfolds to
   `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. The arbitrary explicit universe `u` is retained
   throughout all constructions, including the lifted two-object interval. Verdict: exact.
3. The sole hypothesis on W: `(W : SimplicialSpace.{u}) (hW : IsSegal W)`.
   The recorded `SegalSpace.IsSegal` is Reedy fibrancy of the terminal map and weak
   equivalences of `segalMap W n` for every `n` with `2 ≤ n`. I read its use of
   `Reedy.rightClass (monomorphisms SimplexCategory).op`, and the relative-matching
   definition, confirming that the negative arrows are opposites of injections.
   `pathSpace` uses actual consecutive edges and their endpoint equations in every
   inner degree. This is the stated iterated strict pullback. Verdict: exact.
4. Objects x,y and mapping spaces: `SSet.Segal.mappingFiberSubcomplex` imposes
   `d₁ = constant x` and `d₀ = constant y` on the entire inner simplex, and
   `mappingFiber` takes its simplicial set. `mappingFiberMap t x y` applies t in
   outer degree one, with the naturally induced endpoint vertices. There is no
   replacement, arbitrary comparison map, or loss of the endpoint conditions.
   Verdict: exact.
5. The homotopy category hV: `SSet.Segal.homotopyCategory V` is Mathlib's
   `hoFunctor` on the outer simplicial set of inner vertices. I read the Mathlib
   construction: its objects are the original vertices, its identities are
   degeneracies, and its triangle relations impose degree-two composition.
   I also read the existing `homotopyCategory_homs` signature, which identifies
   its homs with components of `mappingFiber` for Segal spaces, by surjectivity
   of `fiberEdge` and its precise component-equality criterion. Its `IsSegal`
   uses matching-map fibrancy and the same consecutive-edge condition; the
   relative-terminal-matching form used here is the equivalent Reedy-fibrancy
   formulation. No homotopy category is privately defined in this delivery.
   `homotopyFunctor t` is the actual induced functor. Verdict: exact.
6. F(n), cK, and the exponential: the dependency's `discreteRepresentable` and
   `constant` implement the stated outer representables and constant objects.
   `ihom` uses its recorded `instMonoidalClosed`. I read the Mathlib
   functor-category construction and its adjunction: evaluation at bidegree
   (n,q) identifies it with maps from `A × F(n) × cΔ[q]`, and the operators
   are precomposition. Using this canonical adjunction is legitimate even
   though Mathlib constructs the right adjoint abstractly. Verdict: exact.
7. The walking groupoid, E, and its two endpoints: the existing `WalkingIso`
   is `Codiscrete (ULift Bool)`, with precisely two objects and a unique arrow
   per ordered pair. `E` is its nerve made discrete in the inner direction.
   `endpoint false` and `endpoint true` select its two objects. `toFZero` is
   the unique map to the discrete outer zero-simplex. Verdict: exact.
8. The map j induced by collapse: `cotensorConstant W` is
   `MonoidalClosed.curry (snd SSet.Segal.E W)`. Under the exponential
   adjunction this sends w to the constant E-diagram, exactly restriction
   along `E → F(0)` with the terminal-exponent identification. Verdict: exact.
9. Each evaluation p_i: `cotensorEvaluation W i` pairs the constant map
   `toFZero ... ≫ endpoint i` with the identity and composes with
   `(ihom.ev SSet.Segal.E).app W`. The pair has order `E × W^E`, as required
   by the chosen internal-hom adjunction. It is evaluation at the specified
   endpoint, equivalently restriction along e_i. Verdict: exact.
10. DK equivalence: `IsDwyerKanEquivalence t` is precisely
    `(SSet.Segal.homotopyFunctor t).IsEquivalence ∧ ∀ x y, ...`, where the
    second conjunct is weak equivalence of the actual induced mapping-fiber
    map. The quantifier ranges over all original source vertices. The
    predicate needs no Segal proof argument, and all applications in the
    theorem have Segal source and target by hW and the first conjunct.
    Neither essential surjectivity nor the mapping-space condition is omitted.
    Verdict: exact.
11. Every conclusion: the first conjunct is `IsSegal ((ihom E).obj W)`;
    the second is DK equivalence of `cotensorConstant W`; the third is
    `∀ i : Bool, IsDwyerKanEquivalence (cotensorEvaluation W i)`.
    Thus j, p₀, and p₁ have exactly the claimed properties. There are no
    additional hypotheses or conclusions. Verdict: exact.

### Edge cases, searches, and repairs

Empty W is admitted: there is no `Nonempty` assumption. Since E has vertices,
its exponential into empty W is empty as well; the mapping-space quantifier is
vacuous, while the category-equivalence clause is still retained. Empty mapping
fibers for particular x,y are included. A one-object identity-only space and
the discrete nerve of a category with nonidentity isomorphisms are admitted;
the latter checks that completeness was not slipped in. There is no Segal-map
condition beyond the source at n=0 or n=1, both endpoints are covered by Bool,
and no independent universe equality is imposed. Scheme emptiness, coefficients,
and characteristic are inapplicable to this simplicial-space theorem.

I independently repeated the search with different descriptions:

- LeanFinder via `msearch.py`: “For a bisimplicial Segal space restriction of the
  walking groupoid exponential to either object is fully faithful and essentially
  surjective”. Eight hits concern strict nerves and their fully faithful nerve
  functors; none is this Segal-space theorem or these canonical maps.
- Loogle via `msearch.py`: `"cotensor"`, zero hits.
- LeanSearch via `msearch.py`: “The two object indiscrete groupoid yields Dwyer
  Kan equivalences by evaluation on Segal spaces”. Eight hits concern ordinary
  discrete/subgroupoids and contain no matching statement.
- `rg` over Mathlib, the upstream `WeilConjectures` source, the project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, for Dwyer--Kan,
  walking-exponential/cotensor, Segal evaluation/cotensor, and all four new names.
  There is no existing statement or collision. The project does have
  `CategoryTheory.DwyerKanEquivalence`; I opened its signature in
  `CoherentNerveComparison.lean`: it is for enriched functors between
  simplicial categories, not maps of Segal spaces, and cannot replace this
  predicate. The already shared mapping fibers, homotopy category, E and
  endpoints are reused. The neighboring categorical-equivalence theorem
  assumes supplied categorical homotopy inverses, so it is not an exact match.

No mathematical mismatch was found and no Lean or node changes were needed.
There are no new nodes, dependency modules, repair notes, or statement corrections
in this delivery. I verified that only the item's `lean` field differs from the
shared node; no citer audit is triggered. The supplemental definitions-only use
of `SegalCategoricalEquivalence` is legitimate: its eventual reverse proof import
must be omitted by the explicit import-cycle exception, already recorded in the
worker report. No assertion of that downstream theorem is used here. The two
unstated proof dependencies still have no Lean records, so there are no missing
currently available proof imports.

I checked the source/blueprint docstrings, all eight proof steps against the DAG,
and the three definition bodies: all their data are real constructions. The sole
postponed theorem is `cotensor_evaluation_dk`, with exactly `by sorry`. All binders
and universes are explicit, there are no private definitions or local notation,
and every Lean line is at most 100 characters. The node's `lean.statement` is
verbatim equal to the complete signature in the module.

Validation: the prescribed `scompile.py` succeeded on the absolute sandbox file
path, exit 0, with no errors or warnings (sandbox 3.2 s; library path 1.7 s).
This second reading adds this report section only and retains the correct statement.

Delivery dry run: the first wrapper attempt included unrelated maintenance/launcher
files and was rejected before push. Retrying the unchanged sandbox resolved that
tool packaging failure. `deliver2.py Q59 lem-coef-segal-cotensor-evaluation-dk
--no-push` then exited 0 and printed `OK (dry run)` for commit `1b9f26ca00`:
exactly the module, item node, and report were staged; preflight and compile passed.
