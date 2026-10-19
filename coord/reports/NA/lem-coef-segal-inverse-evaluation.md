## Worker report

The module `Sheaf.CategoryTheory.SegalInverseEvaluation` states
`SSet.SegalInverse.segal_inverse_evaluation`. Its proof is `sorry`; all helper
constructions have explicit data and structural proofs. No theorem is proved.
There is no definition chosen from an unproved existence theorem.

I read the item, its complete six-step proof, the statement and full recorded
interface of `def-cbc-enhanced-diagrams-cones`, and the full source module
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. I also read the current recorded
homotopy-Segal interface and its complete module, the Reedy relative-matching
interface, and the canonical path-pullback map and its complete signature and
docstring. There is no repair note for this item.

The node is stated using concrete models of its spaces, following exactly the
model comparison in its proof. These choices preserve its generality:

* The arbitrary `W : SimplexCategoryᵒᵖ ⥤ SSet.{u}` with
  `HomotopySegal.IsHomotopySegalSpace W` represents an object of
  `Fun(Δᵒᵖ, S)`. The predicate requires levelwise Kan values and the canonical
  homotopy-Segal comparisons in every degree `n+2`. Thus the levelwise model
  represents arbitrary space-valued Segal objects, without Reedy fibrancy or
  completeness as an extra hypothesis on W. All universes are explicitly bound.
* The first conjunct supplies a Reedy fibrant replacement for every diagram.
  The main conjunct then applies to EVERY such replacement `i : W ⟶ V`.
  Reedy fibrancy uses the recorded `Reedy.rightClass` on opposite injections
  and the terminal map. It is a specialization of the existing definition,
  not a separate matching-object construction. The objectwise comparison is
  the dependency's realization weak homotopy equivalence.
* For a simplicial set K, `mappingComplex K V` has inner q-simplices the natural
  families `Kₙ → Vₙ,q`. Inner Yoneda identifies these precisely with maps
  `dK × cΔ[q] → V`. In particular `mappingComplex coherentIso V` computes
  `Map_(P_Δ)(dE,W)`, since dE is Reedy cofibrant and V is Reedy fibrant.
  No strict mapping complex into an arbitrary nonfibrant W is substituted.
* J and its nerve E are the EXISTING Mathlib `CategoryTheory.WalkingIso` and
  `SSet.coherentIso`. I read CoherentIso.lean in full. It is the codiscrete
  category on two objects; `coherentIso.hom.edge` is exactly 0 → 1.
  `edgeEvaluation V` evaluates the natural family at this actual edge.
* Mapping spaces W(x,y) are the EXISTING `HomotopySegal.simplexFiber W 1 ![x,y]`:
  the path-model homotopy fiber of `vertices W 1 = (d₁,d₀)`.
  `IsInvertibleClass W x y f` asserts a reverse class g and BOTH inverse
  equations with `HomotopySegal.Composes` and `HomotopySegal.identity`.
  These use exactly the degree-two Segal composition graph and s₀ identity
  from the recorded definition. No arbitrary homotopy category is supplied.
* `edgeClass` puts an edge into its mapping fiber with the constant endpoint
  path. `invertibleArrows W` is the full subcomplex on vertices in the same
  `π₀(W₁)` component as an edge whose class satisfies those inverse equations.
  This is explicitly the UNION OF COMPONENTS W_inv, not just a set of chosen
  invertible arrows or a chosen inverse structure. The full-subcomplex
  construction includes all simplices of each selected component.
* To represent evaluation in the ORIGINAL W₁, `derivedMapping i` is the path
  pullback of `edgeEvaluation V` along `i₁ : W₁ → V₁`. Its data consist of a
  coherent map, an edge of W₁, and a path comparing their images in V₁.
  `toMappingComplex i` forgets the edge and comparison path; the theorem
  expressly makes it a weak equivalence. Thus this pullback is an equivalent
  model of the required derived mapping space, not an arbitrary source.
  `derivedEvaluation i` is its actual W₁ projection. This construction uses
  categorical pullbacks, whose universal property determines them up to iso.
* The conclusion supplies `e : derivedMapping i ⟶ (invertibleArrows W).toSSet`
  with `e ≫ ι = derivedEvaluation i`, and makes e a weak homotopy equivalence.
  Equality after the monic inclusion uniquely determines e; this is a theorem
  about the canonical restriction map, not an unspecified equivalence.
* `derivedEndpoints i` is evaluation followed by `(d₁,d₀)`;
  `inverseEndpoints W` is the invertible-subspace inclusion followed by that
  same map. The factorization equation makes e a map over exactly W₀².
  For EVERY x,y, `evaluationFiberMap i e he x y` is the EXISTING canonical
  `HomotopySegal.fiberMap` over the identity of W₀², and is a weak equivalence.
  The proof parameter he is quantified over all proofs of the factorization.
* The final fiber factor j identifies the homotopy fiber of W_inv over (x,y)
  with `invertibleMappingSpace W x y`. This is the full subcomplex of W(x,y)
  selected by the invertibility of its `π₀` class. The equation
  `j ≫ ι = inverseFiberInclusion W x y` fixes the comparison to the whole
  mapping space. This states the consequent fiber description explicitly.
* The final conjunct states naturality. For every map F between homotopy Segal
  spaces, its map f on invertible subspaces is fixed by equality after ι.
  For EVERY commuting square of replacements i, i', F, G, and EVERY pair of
  evaluation factorizations e,e', the equality
  `derivedMappingMap i i' F G h ≫ e' = e ≫ f` is asserted. The map on derived
  mapping objects is the existing canonical path-pullback map applied to
  postcomposition on mapping complexes, F₁, and G₁ on paths. No arbitrary map
  is inserted. Evaluation/postcomposition are defined in every inner degree,
  so they retain the higher simplicial parameters as well as vertices.
* Completeness is nowhere assumed. The extra quantified replacement objects
  are models of the same W, and existence is included rather than presupposed.

The module docstring explains the concrete-model convention; the theorem
docstring contains all six proof steps, with the original dependency ids.
The node's natural-language statement, proof and proof dependencies are unchanged.
Its statement dependencies only gain the three already recorded nodes whose
interfaces the explicit models use. There are no new nodes or dependency repairs.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `fullSubcomplex`, `evaluation`,
  and `homotopyFiber` (node `def-cbc-enhanced-diagrams-cones`).
* `Sheaf.CategoryTheory.HomotopySegalSpace`:
  `SSet.HomotopySegal.IsHomotopySegalSpace`, `simplexFiber`, `vertexPower`,
  `vertices`, `fiberVertex`, `fiberMap`, `identity`, and `Composes`
  (node `def-coef-homotopy-segal-space`, added to stmt_deps).
* `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.rightClass`, specialized with the opposite of
  `MorphismProperty.monomorphisms SimplexCategory`,
  `HomotopicalAlgebra.fibrations SSet`, and `terminal.from V`
  (node `lem-coef-reedy-model-structure`, already a proof dependency and
  now added to stmt_deps because the fibrancy interface occurs in the type).
* `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`:
  `SSet.Enhanced.simplicialHomotopyPullbackMap`
  (node `lem-coef-kan-homotopy-pullback-invariance`, added to stmt_deps).
* Mathlib primitives: `SSet`, `π₀`, `mapπ₀`, `CategoryTheory.WalkingIso`,
  `SSet.coherentIso`, its `hom.edge`, the scoped Kan-model fibrations,
  categorical pullbacks and their projections. No primitive is redefined.
* Proof-only imports for recorded proof dependencies:
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, and
  `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate` (the four recorded
  nondegenerate-presentation declarations). The Reedy module is also used
  in the statement. The remaining proof dependencies have no recorded Lean
  modules on this snapshot, so there are no such import paths to add.

Edge cases checked mathematically before writing:

* The empty Segal space is allowed: the coherent-map space and W_inv are both
  empty, and the endpoint assertions quantify over an empty type.
* The discrete nerve of [1] has only its two identity arrows in W_inv;
  coherent maps from J are precisely the two constant functors.
* The discrete nerve of BG is allowed for a nontrivial group G. Every arrow
  is invertible; the conclusion identifies the mapping space with G, and
  does not impose the false completeness condition `* ≃ G`.
* A constant diagram on any Kan complex K is homotopy Segal and has all
  morphism classes invertible. The comparison gives K on both sides;
  nontrivial loops and independently varying endpoints are retained by the
  homotopy fibers, rather than replaced with strict fibers.
* Degree zero enters Reedy fibrancy through its matching object. The Segal
  comparisons start in degree two, exactly as in the node. The universe u
  is arbitrary and no equality between unrelated universes is imposed.
* Identity replacements are included when W itself is Reedy fibrant. All
  other objectwise weak-equivalence replacements are also quantified.
* Both inverse equations, both endpoints, and all (including equal) pairs
  x,y occur explicitly. Empty or noninvertible mapping components are not
  dropped by an inhabitation hypothesis.

Searches made through `msearch.py` (recorded in `searches.jsonl`):

* LeanFinder: "For a Segal space evaluation from the walking isomorphism is
  an equivalence onto invertible arrows". Eight hits: strict Segal spine
  bijections and ordinary nerves, none for homotopy Segal spaces.
* Loogle: `SSet.StrictSegal.spineEquiv, CategoryTheory.WalkingIso`. No hits.
* LeanSearch: "Segal space coherent invertible arrows evaluation". Eight
  hits, mostly generic coherence/evaluation results and strict Segal nerves;
  none states the node.
* Mathlib grep: `SegalSpace|walking.?iso|coherentIso` in AlgebraicTopology.
  CoherentIso.lean provides the walking isomorphism (reused here), but
  `WalkingIso.equiv` concerns ordinary functors, and `invStructOfEqMapHom`
  gives specified inverse witnesses, not the equivalence of coherent-map
  spaces. StrictSegal.lean gives bijections for strict simplicial sets,
  not the homotopy-Segal theorem. I read both relevant source definitions.
* Source-project rg: `Segal|mappingComplex|inverseEvaluation|segal_inverse`
  and the exact node id in `WeilConjectures/`: no matches.
* Project rg in `lean/Sheaf`: `SegalInverse|segal_inverse_evaluation|def
  mappingComplex` gives no pre-existing declaration of this interface.
  The broader Segal search found the homotopy-Segal module, which is reused,
  and the distinct DK-diagonal theorem. The classifier node has no recorded
  Lean declaration and is not duplicated as a theorem here: it remains a
  proof dependency in the original six-step plan.
* `dag/lean_names_upstream.json`: no names in the new `SSet.SegalInverse`
  namespace. No full name in this delivery duplicates a source declaration.

Source checked online: https://arxiv.org/html/math/9811037, especially §§5.5,
5.7, Lemma 5.8, Theorem 6.2, square (6.3), and Proposition 11.1. These give
both inverse equations, component saturation, actual edge evaluation, and
its endpoint-fiber interpretation without completeness. No mathematical
statement fault or STATEMENT-DISPUTED flag was found.

Validation: `scompile.py NA lem-coef-segal-inverse-evaluation` compiled the
sandbox and the actual module name cleanly, within the standard 60-second
per-file limit. The required delivery dry run printed OK (commit `38dcbe9942`): compilation and
server preflight passed except for the second-reading section, which the
second reader supplies. Nothing was pushed.

## Second reading by NA

I independently read the node's statement and six proof steps, the delivered
module, and the statements and source declarations of its four original
statement dependencies. I read Rezk's paper online at
https://arxiv.org/html/math/9811037, Sections 2.3–2.5, 4.1, 5.1–5.7,
Theorem 6.2, square (6.3), and Proposition 11.1 and its passage to Theorem 6.2.
This node has no Stacks source. Rezk's convention includes Reedy fibrancy;
the node instead speaks in Fun(Delta^op, spaces). The replacement used here
implements that change of presentation, rather than adding fibrancy to W.

My object/hypothesis/conclusion checklist, matched against the final Lean:

1. Spaces and weak equivalences: `SSet.{u}` with
   `Enhanced.IsWeakHomotopyEquivalence`; the latter is exactly the recorded
   realization predicate, including components and every positive based
   homotopy group. `HomotopySegal.IsHomotopySegalSpace W` includes levelwise
   Kan values. Verdict: the dependency's space convention, with arbitrary u.
2. The ambient simplicial object W: `W : SimplexCategoryᵒᵖ ⥤ SSet.{u}`.
   Its Segal hypothesis is `HomotopySegal.IsHomotopySegalSpace W`, whose
   `comparison W n` covers degree n+2 and uses consecutive edges and joining
   paths. I checked its `targetCondition`, `comparison`, and predicate, not
   just the name. These are homotopy edge products as required. Verdict: all
   degrees at least two, with no strict-Segal or completeness assumption.
3. Discrete dK and coherent maps: `mappingComplex K V` has natural families
   `K_n → V_n,q` in inner degree q. Inner Yoneda identifies them with actual
   maps dK times cDelta[q] to V, with the stated precomposition operators.
   On a Reedy fibrant V this computes the required derived mapping space.
   The first conjunct supplies a replacement for every W; the second applies
   to every such i, with no replacement chosen as data. Verdict: the same
   mapping space in the node's unlocalized presheaf category.
4. J and E: Mathlib's `WalkingIso` is the codiscrete category on two objects,
   and `coherentIso` is its nerve. I read `WalkingIso.equiv`, `coherentIso`,
   both vertices, and both edges. `edgeEvaluation V` evaluates at
   `coherentIso.hom.edge`, specifically 0 to 1. Verdict: the prescribed
   category, nerve, and distinguished edge, without an arbitrary map.
5. Mapping fibers and hW: `HomotopySegal.simplexFiber W 1 ![x,y]` is the
   path-model fiber of `vertices W 1`, whose two coordinates are d1 and d0.
   I read `fiberVertex`, `identity`, `fiberRestriction`, and `Composes`.
   `Composes` uses the three restrictions d2,d0,d1 from the triangle fiber,
   and `identity` is s0 with the constant endpoint path. Verdict: exactly
   the node's morphism components, identities, and composition graph.
6. Invertibility: `IsInvertibleClass W x y f` quantifies a reverse component
   g in W(y,x) and both equations gf=id_x and fg=id_y using that graph.
   Verdict: two-sided invertibility of the specified class; no chosen inverse
   structure and no substitution of mere isomorphism of its endpoints.
7. W_inv: `invertibleArrows W` uses `Enhanced.fullSubcomplex` and explicitly
   saturates the invertible-edge predicate under equality in pi0(W1).
   `edgeClass` supplies the original edge with its constant endpoint path.
   Verdict: the union of components, retaining every simplex in them, as in
   Rezk 5.7 and Lemma 5.8; not a space of specified inverse witnesses.
8. Evaluation in the original W1: `derivedMapping i` is the path pullback
   of `edgeEvaluation V` along i1. Its projection `toMappingComplex i` is
   expressly asserted to be a weak equivalence. `derivedEvaluation i` is
   the actual W1 projection. The existential e is fixed uniquely by
   `e ≫ (invertibleArrows W).ι = derivedEvaluation i`, and e is asserted
   weakly equivalent. Verdict: canonical edge restriction with its specified
   image; the extra model comparison does not replace it by a bare existence
   of equivalent homotopy types.
9. Both endpoints: `derivedEndpoints i` and `inverseEndpoints W` compose
   with exactly `HomotopySegal.vertices W 1`. The factorization equation
   therefore makes e a map over W0 squared. Verdict: both endpoint clauses
   hold with their original order x,y.
10. Consequent fiber statement: for every x,y, `evaluationFiberMap` is the
    dependency's canonical `fiberMap` over the identity of W0 squared and is
    asserted a weak equivalence. The further j factors the canonical
    `inverseFiberInclusion` through `invertibleMappingSpace W x y` and is
    a weak equivalence. This latter subcomplex selects precisely the pi0
    classes satisfying both inverse equations. Verdict: the claimed union
    of invertible mapping components, including its inclusion into W(x,y).
11. Naturality: the final conjunct quantifies every F between the specified
    homotopy Segal spaces. Its restriction f to W_inv is fixed by the equality
    after inclusion. For every commuting square iG=Fi' and all evaluation
    factorizations, it asserts `derivedMappingMap ... ≫ e' = e ≫ f`.
    `derivedMappingMap` is the existing canonical path-pullback map, with
    actual postcomposition on coherent maps, edges, and paths. Verdict:
    naturality of evaluation, not naturality of an unspecified equivalence.
12. No completeness: neither the hypothesis nor any construction asserts
    that s0 is a weak equivalence onto W_inv. Verdict: the node's last clause
    is preserved. Replacement existence is a model-availability assertion,
    not an extra assumption on the given Segal object.

Edge cases checked independently: empty W has empty coherent-map and arrow
spaces, and the fiber quantifiers are empty; the point diagram gives the
identity equivalence. The discrete nerve of [1] selects its two identities.
For the discrete nerve of a nontrivial group G, every arrow is invertible
and both spaces are discrete G, so completeness is not accidentally forced.
A constant diagram on a Kan complex K retains the paths between arbitrary
endpoints in its homotopy fibers; the comparison has homotopy type K.
Equal endpoints, empty mapping spaces, and noninvertible components are all
allowed. Degree zero is included in Reedy matching, while Segal comparisons
begin at degree two. No characteristic, ring, scheme, finiteness, nonempty,
or unrelated universe hypothesis occurs. Every variable and universe is
bound (`autoImplicit false`, `universe u`).

Independent searches used different queries from the first worker:

* LeanFinder: "Rezk equivalence from the space of coherent isomorphisms to
  the subspace of homotopy equivalences in a simplicial space" returned
  ordinary homotopy-category and nerve constructions, not this statement.
* LeanSearch: "Space of functors from the walking equivalence to a Segal
  simplicial space evaluated at its generating arrow" returned ordinary
  functor equivalences and simplex-category declarations, not this theorem.
* Loogle: `SSet.coherentIso, SSet.π₀` returned no hits.
* Mathlib grep: `hoequiv|SegalSpace|equivalenceClassifier|mappingComplex|coherentIso`
  in AlgebraicTopology found the existing walking-isomorphism nerve, which
  is reused. I opened its declaration and the strict-Segal signatures:
  ordinary functors and bijective spines do not state this homotopy-Segal
  mapping-space assertion.
* Direct rg in the source project and `lean/Sheaf` for `mappingcomplex`,
  `homotopy.*segal`, `hoequiv`, and `coherent.*isomorph` found the existing
  homotopy-Segal interface, the different DK theorem, and the Reedy Segal
  modules described below. The upstream declaration-name index contains
  no declaration in this delivery's namespace. I also examined Mathlib's
  complete functor-category internal hom and enriched functor-category end:
  they supply general internal homs, not this edge-evaluation theorem. The
  explicit natural-family construction here is its concrete enriched model
  for a discrete outer source, preserving evaluation in every inner degree.

Mismatch found and repaired (H4): `SegalInverse.IsReedyFibrant` duplicated
the already landed `SSet.SegalSpace.IsReedyFibrant` in
`Sheaf.AlgebraicTopology.SegalCartesianExponent`. I opened that entire module
and its owning node `lem-coef-segal-cartesian-exponent`: its predicate expands
to the identical `Reedy.rightClass` on opposite injections and the terminal
map. I removed the duplicate, imported the owning module, used the existing
fully qualified predicate in the theorem, and added that landed node to
`stmt_deps`. I checked that this dependency has no path back to the item.
The node's declaration list and verbatim signature were updated together.
The worker report's references to the old local predicate describe the
pre-review version and are superseded by this correction.

No source-based statement correction was necessary; the node's TeX, proof,
and proof dependencies are unchanged. There are no new nodes or dependency
modules to audit. All constructions have actual data; only the main theorem
has `sorry`. Its docstring follows all six proof steps and records their
dependency ids. All declarations have source/blueprint docstrings, all lines
are at most 100 characters, and no private notation or extra axiom is used.

Validation: the repaired file compiled through the prescribed `scompile.py`
wrapper, both as its sandbox module (4.8 s) and under its actual module name
(2.0 s), with no errors or unexpected warnings. The node's `lean.statement`
is copied verbatim from the final theorem signature.
