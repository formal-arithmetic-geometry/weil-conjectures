## Worker report

Module: `Sheaf.CategoryTheory.RelativeConeConstantTest`.
Main declaration: `SSet.Enhanced.relative_cone_constant_test`.
All construction data are explicit; the sole postponed theorem is the main declaration,
whose whole proof is `sorry`. Its docstring supplies a five-step natural-language proof.
The item's mathematical statement and dependency list are unchanged. No new nodes or
repairs of dependency modules are needed.

Source read: [Kerodon Proposition the project server](https://kerodon.net/tag/02X1),
conditions (2) and (3), displayed square (7.3), and its proof using right-fibered slices;
also [Proposition the project server](https://kerodon.net/tag/01L5), the canonical pinch comparisons.
The incoming criterion is (2) iff (3); outgoing tests are its colimit dual.
The source place recorded in the node explicitly includes the apex reformulation using
one-sided anodyne restriction to the cone vertex.

Hypotheses and clauses, checked individually against the node:

- Simplicial sets, coherent functors, and the fixed size convention: `K D B : SSet.{u}`.
  `K` is arbitrary; there is no quasicategory assumption on the indexing shape.
  `universe u` and every variable are explicit, with `autoImplicit false`.
- Quasicategory hypotheses: `[Quasicategory D] [Quasicategory B]`.
- The arbitrary functor is `p : D ⟶ B`. No inner-fibration, isofibration, or other
  property of `p` occurs anywhere in the signature.
- The cocone diagram is `q : rightJoinCone K ⟶ D`. Its boundary is exactly
  `rightJoinConeInclusion K ≫ q`, and its apex is the image under `q` of
  `constantTestRightApex K`, the pure final `Δ[0]` factor.
- The induced coherent cocone is retained through the *whole* diagram `q`.
  For a constant target `z`, the canonical composition map of spaces is the roof
  `Map_Fun(K▷,D)(q,Δz) → Map_D(x,z)` (evaluation, the equivalence leg), together
  with `Map_Fun(K▷,D)(q,Δz) → Map_Fun(K,D)(f,Δz)` (restriction, the right leg).
  Naturality of the transformation along the canonical cylinder, with its zero end
  in `K` and its one end at the final apex, identifies this roof with precisely
  `u ↦ Δ_K(u) α`. This uses the entire induced transformation, not a family of
  unrelated edges, an arbitrary comparison map, or a chosen inverse equivalence.
  `constantTestEvaluation` and `constantTestRestriction` implement these two legs.
  Evaluation's target is written using the actual endpoint evaluations: these are
  `x=q(*)` and `z` for outgoing tests, `z` and `x` for incoming tests.
- The first equivalence in the first conjunct states `IsRelativeColimitDiagram p q`
  iff `∀ z : D _⦋0⦌, ConstantApexSquare ... false`. `ConstantApexSquare` is the
  apex square in spaces represented by the two canonical evaluation/restriction
  roofs, in `D` and `B`. It requires the evaluation legs to be weak equivalences
  and the whole-diagram testing square to be a homotopy pullback. This is an
  explicit model for the node's square of spaces considered up to weak equivalence;
  it does not choose a strict composition operation on right-pinched mapping spaces.
- Its four corners are thus `Map_D(x,z)`, `Map_Fun(K,D)(f,Δz)`,
  `Map_B(px,pz)`, and `Map_Fun(K,B)(pf,Δ(pz))`. Its horizontal maps are the
  specified composition roofs. The vertical maps are induced by `p`, namely
  `constantTestPostcomposition` and the corresponding evaluated map.
- Coherent commutativity and the comparison to the path pullback:
  `ConstantTestSquare` applies the dependency's `IsHomotopyPullbackSquare` to the
  actual restriction and postcomposition maps. This predicate requires a commuting
  square and a weak equivalence of its canonical comparison to
  `simplicialHomotopyPullback`. That comparison sends a simplex to its two images
  and the constant path between their equal images. Transport through the
  evaluation equivalences gives the specified coherent apex square and its path.
  The path object is the full internal hom from `Δ[1]`, retaining all higher
  simplices, rather than an equality or a path component used in place of path data.
- The second equivalence in the first conjunct is the equivalent constant-target
  test on `K▷` itself, `∀ z, ConstantTestSquare ... false`. There is no universal
  quantifier over other comparison diagrams on its right-hand side; that is exactly
  the reduction from the original all-diagrams relative-colimit predicate.
- The second conjunct states both dual equivalences for `q : leftJoinCone K ⟶ D`,
  with `IsRelativeLimitDiagram`, `constantTestLeftApex K`, and `incoming = true`.
  The test space is now `Map_Fun(K◁,D)(Δz,q)`, its evaluated endpoints are `(z,x)`,
  and its boundary restriction is `Map_Fun(K,D)(Δz,f)`. Thus its roof represents
  precisely `u ↦ α Δ_K(u)`. The lower row is induced by the same actual `p`.
- The next two conjuncts explicitly assert the evaluation-leg weak equivalences for
  all outgoing and incoming test spaces. They justify the apex models without
  making any choices or assuming the desired comparison maps in the hypotheses.
- Naturality in `p`: the first clause of `ConstantTestNaturality` says that
  restriction followed by postcomposition equals postcomposition followed by
  restriction, as actual simplicial maps of the testing spaces.
- Naturality in restriction: the second clause compares evaluation after *any*
  restriction `i : K ⟶ J` with evaluation at the image vertex. It is an equality
  on every mapping-space simplex, not only its vertices. The third clause supplies
  the analogous equation for postcomposition of evaluation legs by `p`.
  These are the two legs of the same composition roof, so they give naturality of
  the passage between the constant test and the apex test.
- The last clause says explicitly that `orderedJoinFunctor.map (e,𝟙 Δ[0])` and
  `orderedJoinFunctor.map (𝟙 Δ[0],e)` carry the new apex to that same apex, for
  every `e : L ⟶ K`. Substituting these domain maps in the preceding clauses
  restricts the entire diagram `q`, including its coherent cocone/cone, as required.
  This makes no false assertion that arbitrary restriction preserves universality.
- No existence of another limit or colimit is assumed or concluded.

Dependency declarations used, with source signatures and docstrings read:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `evaluation`, `IsWeakHomotopyEquivalence`.
  These are the existing right-pinched mapping-space construction, its simplicial
  functor action, internal-hom vertices/evaluation, and realization weak equivalences.
  The dependency's `constantDiagrams` and coherent comma definitions were also read;
  `SSet.const z` is Mathlib's constant simplicial map whose diagram vertex is `Δz`.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone`, `leftJoinCone`,
  `rightJoinConeInclusion`, `leftJoinConeInclusion`, `IsHomotopyPullbackSquare`,
  `IsRelativeColimitDiagram`, and `IsRelativeLimitDiagram`. This module publicly
  supplies the ordered join, its pure-factor inclusions, and the path-pullback model.
  No private duplicate of any of these constructions is introduced.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`:
  `SSet.Enhanced.enhanced_functor_cone_calculus`, including its
  `QuasicategoryMappingSpaceAssertions`, supplies the functor quasicategories and
  Kan mapping spaces invoked in the proof plan. Its complete signature/docstring
  and the composition-span conventions were read.
- Mathlib: `SSet.const`, `SSet.const_comp`, `CategoryTheory.MonoidalClosed.pre`,
  and `ihom` implement the constant maps, restriction, and postcomposition. The
  endpoint transport in `constantTestPostcomposition` uses the actual equality
  `SSet.const z ≫ p = SSet.const (p.app _ z)`, with no extra mathematical hypothesis.

Edge cases checked before drafting and again after compilation:

- Empty `K`: each cone still has its apex; the test boundary functor object is
  terminal, and the criterion is the relative initial/terminal-object mapping-space
  square. Neither a vertex nor an arrow of `K` is required by the construction.
- Empty `D`: a cone diagram cannot exist because its domain has an apex. The
  corresponding universal quantifiers are correctly vacuous.
- `p = 𝟙 D`: both constant testing squares have identity vertical maps up to the
  canonical endpoint transports and are homotopy pullbacks, as the relative
  predicate requires. Nothing accidentally forces an absolute limit or colimit.
- Terminal `B`: the square reduces to the usual absolute mapping-space criterion.
- Arbitrary disconnected shapes and noninvertible arrows are allowed. There is no
  finite, filtered, nonempty, or equivalence assumption on the boundary.
- Empty individual mapping spaces remain valid Kan spaces and weak equivalences
  are tested by the original definition, including components. No basepoint or
  nonemptiness is introduced.

Searches performed for this item (full remote search outputs are in the sandbox's
`searches.jsonl`):

- `msearch.py ... leanfinder`, query “A relative colimit of quasicategories is
  characterized by homotopy pullback mapping space squares with constant target
  diagrams”: eight hits, including horn-colimit and subcomplex-pushout results,
  relative simplicial homotopies, and ordinary universal colimits. No match.
- `msearch.py ... leansearch`, query “quasicategory relative colimit constant target
  diagrams mapping spaces homotopy pullback”: eight hits on ordinary exact
  colimits, universal colimits, constant cocones, and ordinary pullbacks. No match.
- `msearch.py ... loogle`, query `"Quasicategory", "constant"`: zero hits.
- `msearch.py ... grep`, query
  `RelativeColimit|RelativeLimit|homotopyPullback|rightJoinCone` under
  `AlgebraicTopology`: zero hits.
- `rg` in upstream `WeilConjectures` for relative limits/colimits found only ordinary
  relative limit presentations and unrelated geometric uses; the exact node-id
  search found nothing. The side-library search found the recorded definitions and
  references to this unstated theorem in downstream proof docstrings, with no
  declaration of the constant test. In particular no downstream module is imported.
- Exact-name searches for all twelve proposed declarations across Mathlib,
  upstream `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  returned no collisions.

Validation: `scompile.py Q109 lem-coef-infinity-relative-cone-constant-test` compiled
`RelativeConeConstantTest.lean` cleanly, including the module under its actual import
name. The first attempt exposed the nondefinitional constant-endpoint transport under
postcomposition; it was repaired using `SSet.const_comp` and the next compile passed.
There are no errors or warnings. Every line is at most 100 characters. The main theorem
is the only `sorry`. The node copy changes only `lean`.

## Second reading by Q109

I read the node statement and all five proof steps, the delivered Lean, the three
original statement-dependency nodes and their actual modules, and the landed owner
of the apex reused below. The source is Kerodon, not Stacks: I opened
[Proposition the project server](https://kerodon.net/tag/02X1), including conditions (2), (3),
square (7.3), and the right-fibration proof, and
[Proposition the project server](https://kerodon.net/tag/01L5). The former assumes an arbitrary
functor between infinity categories and an arbitrary simplicial indexing set;
it does not assume a fibration of the given functor. The source and the node agree.
There is no existing statement correction and no maintenance repair note for this item.

My object/hypothesis/conclusion inventory and its match to the final Lean:

1. Fixed sufficiently large universes; a small simplicial set K and quasicategories
   D and B. Lean: `universe u`, `(K D B : SSet.{u})`,
   `[Quasicategory D] [Quasicategory B]`. Verdict: exact fixed-universe convention;
   K has no quasicategory, finite, filtered, inhabited, or edge-inversion assumption.
2. An arbitrary functor p. Lean: `(p : D ⟶ B)`. Verdict: exact; no fibration,
   isofibration, equivalence, or existence hypothesis is present.
3. A right cone q, its actual boundary f, apex x and induced coherent cocone alpha.
   Lean: `∀ q : rightJoinCone K ⟶ D`, `rightJoinConeInclusion K ≫ q`, and
   `q.app _ (rightConeApex K)`. `rightJoinCone` is the recorded terminally augmented
   ordered join and the inclusion is its pure K factor. The two canonical legs
   `constantTestEvaluation` and `constantTestRestriction` use this very q on every
   simplex. Thus they represent composition by the coherent cocone of q, not an
   arbitrary comparison map or a family of unrelated edges. Verdict: exact model
   of the node's map of spaces up to weak equivalence. The whole transformation
   contains its naturality along the canonical join cylinder, whose boundary end
   is K and other end is the final apex; this identifies the represented map with
   `u ↦ Δ_K(u) alpha` and retains its higher coherence.
4. For every vertex z of D, the colimit apex square is a homotopy pullback iff q is
   a p-colimit diagram. Lean: the first equivalence in the first conjunct,
   `IsRelativeColimitDiagram p q ↔ ∀ z, ConstantApexSquare ... false`.
   `constantTestSource`/`constantTestTarget` put q before the constant z when the
   Bool is false. Their evaluated endpoints are x,z; after restriction they are
   f,Δ_K z. The two lower endpoints are px,pz and pf,Δ_K(pz).
   `constantTestPostcomposition` uses the actual p and `SSet.const_comp`, not an
   extra hypothesis about constants. Verdict: all four corners, arrows, and
   quantifiers match the displayed square.
5. The coherent homotopy and full path comparison must be retained. Lean:
   `ConstantTestSquare` applies the dependency's `IsHomotopyPullbackSquare` to
   actual restriction and postcomposition maps. Its existential equality witnesses
   the strictly commuting whole-diagram square, and `homotopyPullbackComparison`
   maps into `simplicialHomotopyPullback` using the constant interval, in every
   degree. `ConstantApexSquare` uses that square and its two canonical evaluation
   weak equivalences. Inverting those legs gives the apex square and its coherent
   path. Verdict: a canonical span presentation of precisely the requested square
   of spaces; no path components, pointwise equality, or arbitrary choice replaces
   the internal-hom path data. Requiring the evaluation equivalences is justified
   by their explicit unconditional cone clauses in this same theorem.
6. Equivalently, constant target test diagrams suffice on the whole right cone.
   Lean: the second equivalence in the first conjunct with
   `ConstantTestSquare p (rightJoinConeInclusion K) q z false`.
   Verdict: exact. The test varies over vertices z, not over all cone diagrams;
   the all-diagrams predicate remains the recorded `IsRelativeColimitDiagram`.
7. Dual left cone, apex x, boundary f, incoming square and constant-source test.
   Lean: the second conjunct with `leftJoinCone`, `leftJoinConeInclusion`,
   `constantTestLeftApex` and `incoming = true`. Now the test mapping space has
   source Δz and target q, evaluation has endpoints z,x, and restriction has
   endpoints Δ_K z,f. The bottom row is obtained by p. Verdict: both dual iff
   clauses and the incoming composition `u ↦ alpha Δ_K(u)` are present.
8. Passage from whole-diagram tests to apex tests. Lean: the next two conjuncts
   assert the weak equivalences of `constantTestEvaluation` for every outgoing
   right cone and incoming left cone. The theorem is universally polymorphic in
   D,B and p, so the same assertions apply in B (also directly encoded by
   `ConstantApexSquare`). Verdict: the source's apex restriction identifications,
   without selecting an inverse or assuming them in the hypotheses.
9. Naturality in p and arbitrary restriction L→K, including the induced coherent
   cones, with apex unchanged. Lean: `ConstantTestNaturality`. Its first equation
   says restriction/postcomposition commute as simplicial maps. The next equation
   compares evaluation after any restriction i with evaluation at i(a), and the
   third compares evaluation after p with p after evaluation. These quantify over
   every simplex of every dimension; taking subtype `.1` forgets only the endpoint
   proofs. The last equations apply the two induced join maps to the actual pure
   apex and leave it fixed. Restricting the entire q along those join maps retains
   its coherent cone. Verdict: the two legs of the composition spans and their
   cone restrictions have the required naturality. There is no assertion that
   changing shape preserves universality.
10. No existence of other limits/colimits. Lean has only universal predicates and
    the two tests, with no existence data or additional assumptions. Verdict: exact.

Dependency signatures and data checked: `EnhancedDiagramsCones.mappingSpace` has
n-simplices with the full initial face constant and final vertex fixed;
`mappingSpaceMap` acts on their underlying simplices. `diagramVertex` uses the
internal-hom vertex of an actual simplicial map; `evaluation` is restriction at
that vertex and `constantDiagrams` is the adjoint of projection. The weak-equivalence
predicate checks realization components and every positive based homotopy group.
`RelativeInfinityCone.IsRelativeColimitDiagram` and `IsRelativeLimitDiagram` quantify
over all comparison join diagrams, respectively outgoing and incoming, with the
same restriction/postcomposition square and full path model. I opened these exact
definitions, not merely their names. `EnhancedFunctorConeCalculus` asserts
quasicategorical internal homs and Kan right-pinched mapping spaces, and uses
canonical composition spans as well. None of these interfaces needs a repair.

Edge cases: with K empty the join still has its pure apex and the boundary functor
space is terminal, giving the relative initial/terminal test. With D empty there
is no cone map, and each relevant universal quantifier is correctly vacuous.
Individual mapping spaces may be empty; their weak equivalences still test
components and require no basepoint chosen in an empty space. For p the identity,
the vertical maps are identities up to the constant-endpoint transport, so the
relative predicate does not impose absolute universality. For terminal B the
criterion specializes to the usual absolute mapping-space test. Disconnected K,
noninvertible boundary edges, dimension zero, and arbitrarily large fixed u are
allowed. Rings, characteristic, zero modules and schemes do not occur in this
statement, so there is no omitted corresponding restriction.

Independent searches used different words from the first worker:

- `msearch.py ... leanfinder`: "A functor between infinity categories has relative
  universal cones detected by morphisms to constant diagrams and evaluation at the
  terminal cone vertex". Eight hits, on ordinary eventually constant cones,
  liftable cones, final functors, and related ordinary results; no match.
- `msearch.py ... leansearch`: "Constant source diagrams detect relative limit cones
  in quasicategories through homotopy cartesian mapping space squares". Eight hits
  on ordinary constant cones and ordinary pullback/limit comparisons; no match.
- `msearch.py ... loogle`: `"Quasicategory", "mapping"`. Zero hits.
- `rg` in Mathlib, upstream WeilConjectures, and `lean/Sheaf`, using both exact
  proposed names and `constant.*(relative|cone|colimit|limit)` / its reverse,
  found no existing theorem. The project hits were the recorded definitions,
  ordinary-category results, and downstream references to this node, not an
  existing implementation of the constant-test criterion.
- A further notion search for apex/vertex and ordered-join inclusions found the
  exact existing final apex `SSet.Enhanced.rightConeApex` in
  `Sheaf.CategoryTheory.JoinSliceDiagramIsomorphisms`. I opened its definition,
  its owning node `lem-coef-join-slice-diagram-isomorphisms`, and its recorded
  declaration list. Its formula is identical to the proposed right-apex helper,
  including the empty boundary. The other apex-related hits are projections
  from comma categories or varying cones, not this vertex. No existing left
  pure-apex helper or constant-testing constructions were found.

Mismatches found and repaired:

- H4: removed the duplicate `constantTestRightApex`, replaced every use by the
  landed `rightConeApex`, and publicly imported its owning module. Added that
  landed owner to `stmt_deps`, as expressly permitted by brief §5. A read-only
  traversal of its statement/proof dependencies found no path back to this item;
  its addition introduces no dependency cycle. No new node or dependency repair
  module was necessary.
- Stage-2 rule 7: added all ten missing ordinary imports for recorded proof
  dependencies that have modules. The three original public imports already
  covered the other proof dependencies. An import-closure check found no path
  back to the present module. These imports provide the plan's dependencies to
  stage 3 without exposing them as statement imports.
- H8: replaced the alternative short proof argument in the theorem docstring by
  the node's complete five-step proof, with its named dependencies. In particular
  it now includes the varying-boundary formula, constant-source specialization,
  strictification of specified coherence paths before fibration calculations,
  the opposite/subdivision/Ex-infinity comparison and its product compatibility,
  and the final naturality calculation. Reflowed a long displayed formula to
  obey the 100-character line limit.

The signature is unchanged except for reuse of the existing apex name. The node's
mathematical statement, proof and proof dependencies are unchanged; only `lean`
and the one permitted addition to `stmt_deps` changed. I synchronized
`lean.statement` verbatim with the final signature and removed the obsolete name
from `lean.declarations`. All eleven remaining declarations have source/blueprint
docstrings. All definitions have actual construction data; the sole `sorry`
is the named main theorem. No new theorem was proved, no private/local definition
or notation hides a binder, and every universe and variable is bound explicitly.

Validation: the repaired module compiled via the required `scompile.py` under its
sandbox and actual library module names, within the default single-file timeout.
The full node proof initially exposed one line-length warning; that line was
reflowed and compilation then passed with no errors or warnings. The final apex
reuse is compiled again before delivery. Server preflight is run through
`deliver2.py --no-push`, followed by the actual delivery.
