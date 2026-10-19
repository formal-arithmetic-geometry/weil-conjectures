## Worker report

`Sheaf.AlgebraicTopology.SegalEquivalenceOuterHorn` states Rezk Section 11.7,
Lemma 11.10. It gives actual definitions of the mapping complex, all-equivalence
subcomplex and restriction map; its only postponed theorem is
`SSet.SegalSpace.equivalence_outer_horn`. Definitions contain real data; their
functoriality and subtype-membership proofs are complete. No mathematical theorem
is proved at this stage. The source PDF was opened online, especially Section 11.7,
Lemma 11.10 and the face-cover proof of Lemma 11.11.

Every clause and hypothesis is rendered as follows:

- A small simplicial space is `V : SSet.SegalSpace.SimplicialSpace.{u}`, the
  recorded functor `SimplexCategoryᵒᵖ ⥤ SSet.{u}`.
- Reedy fibrancy and all consecutive-edge weak equivalences for degrees at least
  two are exactly `hV : SSet.SegalSpace.IsSegal V`. The recorded definition uses
  `Reedy.rightClass` on the terminal map with opposite-injective negative arrows,
  and `Enhanced.IsWeakHomotopyEquivalence` on the consecutive-edge maps.
- The strict fibers M_V and invertibility in hV are represented by the existing
  `CategoryTheory.SegalSpace.mappingSpace`, `SameMappingComponent`, and
  `IsEquivalenceArrow` definitions: an inverse and two triangles whose long edges
  have the identity classes in the strict mapping fibers. These are the node's
  inverse equations for the degree-two Segal composition.
- V_eq is the existing `CategoryTheory.SegalSpace.equivalenceArrows`, the full
  subcomplex on the union of components containing inverse-equation arrows.
  `uncurriedRowIso` is the canonical identity on inner simplices identifying its
  bisimplicial row with V_1. It adds no data or assumption.
- F(n) is the recorded `discreteRepresentable n`; `constant K` is the recorded cK.
- `mappingComplex X V` has q-simplices literally
  `X ⊗ constant (SSet.stdSimplex.obj q.unop) ⟶ V`. Its operators precompose with
  `id_X × cΔ(α)`, as required. Products are the existing degreewise cartesian
  tensor products.
- `mappingEdgeEvaluation X V e` evaluates the restriction along
  `e : discreteRepresentable 1 ⟶ X` on the identity outer edge and identity inner
  q-simplex. This is the canonical Yoneda identification with V_1, and its
  naturality is proved explicitly.
- `equivalenceMappingSubcomplex X V` is the infimum over ALL those edge maps of
  the preimage of V_eq along this evaluation and the canonical row isomorphism.
  Thus it states the degreewise intersection in the node, retaining all inner
  simplices and every edge evaluation, including degenerate edges.
- `outerHornInclusion k` makes Mathlib's `(horn k 0).ι` discrete in the inner
  direction. Mathlib defines this horn by the image of the ordinal map together
  with {0} failing to cover all vertices, precisely omission of a vertex other
  than zero. It is the stated union of faces 1,...,k.
- `equivalenceMappingRestriction j V` sends a mapping simplex to its actual
  precomposition by `j × id`. Its subtype proof tests `e ≫ j`, so it is exactly
  the canonical restriction and assumes no preservation hypothesis.
- `k : ℕ` and `hk : 2 ≤ k` include every integer in the stated range, with none
  omitted. The theorem concludes exactly
  `Enhanced.IsWeakHomotopyEquivalence
    (equivalenceMappingRestriction (outerHornInclusion k) V)`.

Dependencies read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`
  and `SSet.Enhanced.IsWeakHomotopyEquivalence`; the latter tests bijectivity on
  path components and every positive based homotopy group of realization.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` fixes the Kan--Quillen classes and
  their model structure and right properness.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.model_structure`, `matchingFrom`, `relativeMatching`
  and `rightClass`, for the recorded Reedy definitions.
- `Sheaf.AlgebraicTopology.SegalCartesianExponent`:
  `SSet.SegalSpace.SimplicialSpace`, `discreteRepresentable`, `constant`, `IsSegal`,
  and `cartesian_exponent`. Added this already-landed node to stmt_deps because
  its definitions are used in the signature.
- `Sheaf.CategoryTheory.SegalSpace`:
  `CategoryTheory.SegalSpace.mappingSpace`, `SameMappingComponent`,
  `IsEquivalenceArrow`, and `equivalenceArrows`. Added this already-landed
  definition node to stmt_deps to reuse the existing V_eq construction.

The imports publicly expose the statement dependencies, including the two newly
cited landed nodes. The already-stated proof-only dependencies are imported
privately: KanFibrationArbitraryBaseFibers, RealizationCylinder, and
HomotopyGroupsBasepointChange. The proof dependencies
lem-coef-segal-homotopy-category-components,
lem-coef-segal-composition-equivalences, and lem-coef-segal-finite-cover-descent
have no recorded Lean module in the current node files; their natural-language
proof roles are retained in the seven-step theorem docstring.

The initial candidate import `SegalCategoricalEquivalence` was excluded after a
full DAG closure audit showed it reaches the present item through cotensor
 evaluation and the equivalence classifier. The earlier SegalSpace definition
has no such dependency. No downstream theorem is used, and no dependency node
or source statement is changed.

Edge cases checked before writing: k=2 gives the fork edges 01 and 02, not the
inner spine; k=0 and k=1 are exactly excluded by the source's k≥2 condition;
empty V is allowed and both selected mapping spaces are empty for these nonempty
shapes; the point and discrete category nerves give the expected unique/fork
extensions when every edge is invertible; no completeness or nonemptiness
assumption occurs. Degenerate edges are tested. Arbitrary small simplicial spaces
are allowed in the mapping definitions, including the empty source, whose edge
index set is empty and whose intersection is top. The single universe u imposes
no finiteness or cardinality bound beyond the stated smallness convention.

Searches (the msearch wrapper stores verbatim logs in searches.jsonl):

- LeanFinder: “Segal space restriction to outer horn is weak equivalence on
  equivalence edge mapping subspaces”; eight hits, all strict Segal/horn or
  truncated-simplex results; no Reedy-fibrant Segal-space theorem.
- Earlier wrapper LeanFinder: “Segal space restriction simplex outer horn all
  equivalence edges weak equivalence”; eight strict Segal/truncated hits.
- Earlier wrapper LeanSearch: “Segal space restriction to outer horn equivalence
  edges weak homotopy equivalence”; eight primitive horn/strict-Segal hits.
- Loogle: `SSet.Subcomplex.preimage`; twelve hits giving the preimage API used
  here, not the theorem. Earlier query
  `SSet.horn, SSet.Subcomplex.preimage, SSet.Subcomplex.lift` had no hits.
- Wrapper grep `Segal|segal|outerHorn|outer_horn`, subdirectory AlgebraicTopology:
  25 hits, concerning strict Segal sets and horn constructions.
- rg in the upstream WeilConjectures source for Segal/simplicial-space names:
  no matching construction or theorem; literal blueprint-id grep also no hit.
- rg in lean/Sheaf for mapping spaces, Segal spaces, equivalenceSubcomplex and
  equivalenceArrows found the existing definitions reused here and no matching
  outer-horn theorem. Read their full definitions and docstrings rather than
  relying on names. Read Mathlib Horn.lean and Subcomplex.lean as well.

Validation: scompile.py compiled the sandbox and named library module cleanly,
with no warnings or errors (the only theorem proof is the expected sorry).
No STATEMENT-DISPUTED flag, source correction, new node or dependency repair.

## Earlier second reading (a previous round; superseded)

I independently opened the node, the sandbox module, the dependency declarations,
Mathlib's horn and closed-category definitions, and Rezk's online PDF. The source
is Rezk Sections 2.3--2.5, 4.1, 5.1--5.8 and 11.7--11.11 (printed pp. 26--27
for the item). It is not a Stacks statement. Section 11.7 fixes a Segal space,
without completeness, and defines the all-edge subspace before Lemma 11.10.
The source and the node agree; no statement correction is required.

The following is my object/hypothesis/conclusion checklist, with the final Lean
rendering and verdict for every item:

- Small simplicial spaces V and X: `SimplicialSpace.{u}` is the existing
  `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. First coordinate is outer, second is inner.
  Verdict: exact; arbitrary universe u, no finiteness or nonemptiness hypothesis.
- Reedy fibrancy of V: `hV : IsSegal V` includes `IsReedyFibrant V`, defined as
  `Reedy.rightClass` for the terminal map with opposite monomorphisms in the
  simplex category as the negative arrows. I read `relativeMatching` and
  `rightClass`: these are the matching pullbacks, not an objectwise substitute.
  Kan fibrations are the recorded horn-lifting class. Verdict: exact.
- Consecutive-edge Segal equivalences for every n >= 2: the other conjunct of
  `IsSegal` is `∀ n : ℕ, 2 ≤ n → Enhanced.IsWeakHomotopyEquivalence (segalMap V n)`.
  Its `pathSpace` uses `SSet.Path` with vertices, n consecutive edges and endpoint
  equalities, hence the strict iterated fibre product. Verdict: exact.
- Vertices x,y and strict M_V(x,y): the reused
  `CategoryTheory.SegalSpace.mappingSpace` is the pullback of `(d₁,d₀)` along
  the constant point `(x,y)`. This is used through the equivalence-arrow predicate,
  not assumed as extra data. Verdict: exact, including empty strict fibres.
- Homotopy-category identities, composition and invertibility: I read
  `SameMappingComponent` and `IsEquivalenceArrow`. The former compares pi-zero
  classes in that strict fibre. The latter asks for an inverse and two actual
  outer triangles with consecutive edges a,g and g,a, whose long edges have the
  identity classes at the source and target. For a Segal space, the degree-two
  Segal map is a trivial Kan fibration, so this is precisely invertibility for
  the node's composition. Verdict: exact; no chosen composition or arbitrary
  category structure is added to the hypotheses.
- V_eq: `equivalenceArrows` is the full subcomplex on vertices in components
  containing such an inverse-equation arrow. Its component predicate and
  `Enhanced.fullSubcomplex` retain exactly the union of those components.
  `uncurriedRowIso` is identity on all inner degrees and only transports between
  curried and uncurried notation. Verdict: exact, canonical, no extra witness.
- F(n), for every n >= 0: reused `discreteRepresentable n` is the outer standard
  simplex followed by the constant functor into inner simplicial sets. Thus its
  values are precisely the ordinal hom sets, discrete in the inner direction.
  Verdict: exact, also at n = 0.
- cK: reused `constant K` is constant in outer degree. Verdict: exact.
- Map(X,V)_q and precomposition: final code uses the already-landed
  `SSet.SegalSpace.mappingSpace` and `mappingSpacePre`, from
  `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`. The former is outer
  degree zero of the cartesian internal hom; the adjunction and Yoneda identify
  its q-simplices canonically with `X × cΔ[q] ⟶ V`, since F(0) is terminal.
  The latter is degree zero of `MonoidalClosed.pre`. Verdict: exact, with the
  existing library construction reused instead of a second presentation.
- Every edge evaluation Map(X,V) -> V_1: `mappingEdgeEvaluation X V e` evaluates
  the existing counit `(ihom.ev X).app V` on the identity outer edge supplied
  by e and the outer degeneracy of the internal-hom degree-zero simplex.
  Under the preceding adjunction this is evaluation on the identity inner
  q-simplex, so it is exactly restriction along e followed by Yoneda.
  Verdict: canonical evaluation; no arbitrary comparison map or extra condition.
- T_V(X), in every inner degree: `equivalenceMappingSubcomplex X V` is the
  infimum of preimages of `equivalenceArrows`, over all
  `e : discreteRepresentable 1 ⟶ X`. Verdict: exact intersection; all maps,
  including degenerate edges, are tested, with no loss of higher simplices.
- H(k) and its inclusion into F(k): `outerHornInclusion k` is the inner-discrete
  whiskering of `(horn k 0).ι`. I read Mathlib `horn`, `horn_eq_iSup` and
  `mem_horn_iff_notMem_range`: membership means omitting some vertex different
  from zero, equivalently union of all faces indexed 1,...,k. Verdict: exact.
- Canonical restriction T_V(F(k)) -> T_V(H(k)):
  `equivalenceMappingRestriction (outerHornInclusion k) V` has underlying map
  `mappingSpacePre`. Membership follows from the test `e ≫ j`; its verification
  uses naturality of `MonoidalClosed.pre` and the library counit compatibility
  `id_tensor_pre_app_comp_ev`. Verdict: actual restriction, with no added
  preservation hypothesis or freely chosen morphism.
- Range and quantifier order: the final theorem binds V, `hV : IsSegal V`,
  `k : ℕ`, and `hk : 2 ≤ k`. Natural numbers with that bound are exactly the
  integers in the node's range. Verdict: all k >= 2, no omitted case.
- Conclusion: `Enhanced.IsWeakHomotopyEquivalence` of that specific restricted
  map, whose domain and codomain are precisely the two selected subcomplexes.
  I read its definition: bijection on realization path components and every
  positive based homotopy group at every basepoint. Verdict: exactly the node's
  conclusion, with neither a stronger fibration conclusion nor an extra clause.

Edge cases: k = 2 gives the fork 01 and 02, not the inner spine; k = 0 and
k = 1 are excluded exactly by the source bound. V may be empty; both mapping
spaces for these nonempty shapes then have no vertices, with no artificial
inhabitedness assumption. Terminal V and discrete category nerves give the
expected all-invertible-edge condition. The auxiliary definitions also allow
empty X: the edge index type is empty and its infimum is top. Degenerate edges
are included. The one universe u ranges over arbitrary small simplicial sets;
the simplex category is small, its hom sets are lifted by the standard simplex,
and the functor hom type is in the same universe. There is no extra universe
identification, field, characteristic, scheme, ring or zero-object assumption.

Independent searches used different terms from the first worker:

- msearch LeanFinder: `simplicial function complex evaluation representable
  invertible arrows Rezk`; eight hits concerning ordinary representability,
  simplicial enrichment and Yoneda; no Reedy-fibrant Segal outer-horn theorem.
- msearch Loogle: `"ihom", "pre", "ev"`; no hits. Direct reading of Mathlib's
  `Monoidal/Closed/Basic.lean` found the counit and its precomposition law used
  in the repair; this is not the theorem being stated.
- msearch grep: `hoequiv|equivalence_outer|mappingSpacePre|mappingEdge`, with
  `AlgebraicTopology`; no hits in the searchable Mathlib index.
- Independent rg in Mathlib's algebraic topology files and in the full upstream
  WeilConjectures tree, using `Segal`, `Rezk`, `hoequiv`, `outer.?horn`,
  `mappingComplex` and `mappingEdgeEvaluation`: the relevant Mathlib results
  concern strict Segal simplicial sets or ordinary horn fillers, and upstream
  has no match. These are not the two-dimensional Reedy-fibrant statement.
- Independent rg in project `lean/Sheaf` found the already-landed
  `SimplicialSpaceReedyCartesian.mappingSpace` and `mappingSpacePre`. I opened
  their definitions and their node record. This found the H4 issue below.
  Other project outer-horn results concern quasicategories or marked lifting,
  not weak equivalences between the all-equivalence mapping subspaces here.

Mismatch found and repaired: the first worker's `mappingComplex` and
`mappingRestriction` duplicated the existing mapping-space notion and canonical
restriction in `SimplicialSpaceReedyCartesian` (H4). I removed both definitions
and their lean.declarations entries, imported and cited the already-landed
`lem-coef-simplicial-space-reedy-cartesian`, and rewrote edge evaluation using
its internal-hom counit. The selected subcomplex and its restriction now use
`mappingSpace` and `mappingSpacePre` directly. The Lean theorem signature and
natural-language statement are unchanged. The worker report above is retained
as requested; its references to the removed two definitions are superseded by
this reading and repair. There are no new nodes or dependency modules to audit.

I also checked all docstrings, the seven-step theorem proof plan against the
node, source/blueprint tags, and the published dependencies' signatures. The
only postponed theorem is `equivalence_outer_horn`, with proof `sorry`.
Definitions have real data; the completed proof fields only establish
naturality and subtype membership. No mathematical theorem has been proved.
No unbound variables, file-local notation, private definitions or local
instances occur. lean.statement is verbatim the signature in the module.

Validation after the repair: prescribed scompile.py compiled the sandbox and
named library module cleanly under the normal 60-second per-file limit; no
errors or warnings. The delivery contains one module and the item node only,
plus this report. No source correction, target change or disputed statement.

## Second reading by Q02

I independently read the current sandbox node and module, the six statement
 dependency records and their source declarations, and Rezk's PDF online at the
URL recorded in the node. The relevant places are Sections 2.3--2.5, 4.1,
5.1--5.7, and 11.7--11.11 (printed pp. 26--27 for the last places). This is a
Rezk statement, not a Stacks statement. Section 11.7 assumes a Segal space;
Section 4.1 includes Reedy fibrancy. Completeness is not assumed. There is no
statement_change, repair note, new node, or dependency module in this delivery.

My object/hypothesis/conclusion checklist, prepared from the node, is:

1. Simplicial spaces V and X: `SimplicialSpace.{u}` is the recorded
   `SimplexCategoryᵒᵖ ⥤ SSet.{u}` from SegalCartesianExponent. Verdict: exact
   two simplicial directions, arbitrary small objects, no nonemptiness added.
2. Reedy fibrancy of V: `hV : IsSegal V` includes `IsReedyFibrant V`, namely
   `IsReedyFibration (terminal.from V)`. I read `Reedy.rightClass` and
   `relativeMatching`: the property requires Kan fibrations of the actual
   matching pullback maps, indexed by opposite injections. Verdict: the
   source's Reedy condition, not merely objectwise fibrancy.
3. Every consecutive-edge weak equivalence for n >= 2: the second conjunct
   of `IsSegal` is `∀ n : ℕ, 2 ≤ n →
   Enhanced.IsWeakHomotopyEquivalence (segalMap V n)`. `pathSpace` has n
   composable edges with their common endpoint equalities via `SSet.Path`.
   Verdict: the strict iterated fibre product and correct full degree range.
4. Vertices x,y and strict M_V(x,y): these are used through the recorded
   `CategoryTheory.SegalSpace.mappingSpace`, the pullback of `endpoints`
   `(d₁,d₀)` over the constant point `(x,y)`. Verdict: exact strict fibres,
   including empty fibres; no additional choices or hypotheses in the theorem.
5. Identity, composition, and invertibility in hV:
   `SameMappingComponent` compares pi-zero classes in those strict fibres.
   `IsEquivalenceArrow` supplies an inverse and two actual outer triangles,
   with long edges in the identity classes at the respective endpoints.
   The Segal map is a trivial fibration for a Segal space, so the triangle
   witnesses give exactly the two inverse equations for its composition.
   Verdict: exact invertibility, without demanding literal identity long edges.
6. V_eq as a union of components: the recorded `equivalenceArrows` uses
   `Enhanced.fullSubcomplex` and the predicate of lying in a component
   containing an `IsEquivalenceArrow`. I read both definitions. Because the
   predicate is component saturated, this retains exactly the specified
   components and all their simplices. `uncurriedRowIso` is identity in every
   inner degree. Verdict: exact, canonical transport between presentations.
7. F(n), n >= 0, and cK: `discreteRepresentable n` is `stdSimplex.obj ⦋n⦌`
   followed by the constant functor in the inner direction; `constant K` is
   constant in the outer direction. Verdict: the recorded source objects,
   also at n = 0, not diagonal simplicial sets.
8. Map(X,V) and its simplicial operators: `mappingSpace X V`, read in
   SimplicialSpaceReedyCartesian, is outer degree zero of the existing `ihom`.
   The adjunction and F(0) terminality give its q-simplices canonically as
   maps `X × cΔ[q] → V`. `mappingSpacePre` is outer degree zero of
   `MonoidalClosed.pre`. Verdict: the existing simplicial mapping complex
   with precomposition operators, with no duplicate construction.
9. Every map F(1) -> X and its edge evaluation: `mappingEdgeEvaluation X V e`
   evaluates the internal-hom counit at the identity outer edge supplied by e.
   The outer degeneracy from degree zero implements the unique map F(1) -> F(0).
   Under the same adjunction it evaluates the inner simplex at its identity.
   Verdict: canonical restriction and Yoneda evaluation, for every e, including
   degenerate edges; no arbitrary comparison or preservation assumption.
10. T_V(X) in every inner degree: `equivalenceMappingSubcomplex X V` is the
    infimum over `e : discreteRepresentable 1 ⟶ X` of preimages of V_eq along
    this evaluation. Verdict: the complete degreewise intersection, not a
    condition only on selected nondegenerate edges or on vertices alone.
11. H(k) and its inclusion: `outerHornInclusion k` is the whiskering of
    `(horn k 0).ι` by the inner constant functor. I read Mathlib Horn.lean:
    `horn_eq_iSup` is the union of faces with index different from zero;
    `mem_horn_iff_notMem_range` requires an omitted vertex other than zero.
    Verdict: exactly the faces 1,...,k specified in the node.
12. Canonical restricted map: `equivalenceMappingRestriction j V` applies
    the recorded `mappingSpacePre j V` to its underlying simplex; the
    membership proof uses the edge `e ≫ j`. I checked the counit compatibility
    and the naturality equation used there. Verdict: actual restriction
    T_V(Y) -> T_V(X), with real data and no assumed auxiliary map.
13. Quantifiers: `V`, `hV : IsSegal V`, `k : ℕ`, `hk : 2 ≤ k` in that order.
    Verdict: every Segal space and every source integer k >= 2; no additional
    typeclass, completeness, finiteness, or inhabitedness hypothesis.
14. Conclusion: `Enhanced.IsWeakHomotopyEquivalence
    (equivalenceMappingRestriction (outerHornInclusion k) V)`. I read the
    predicate: realization induces a bijection on components and on all
    positive based homotopy groups at every basepoint. Verdict: precisely
    the weak homotopy equivalence requested, with no extra conclusion.

Edge cases: k = 2 has edges 01 and 02, confirming the outer fork rather than
an inner spine. k = 0,1 are excluded exactly by the source hypothesis. Empty V
is allowed and both mapping subspaces for the nonempty horn/simplex are empty.
Terminal V gives a point on both sides. Discrete category nerves reduce the
condition to invertibility of all arrows, as expected. Auxiliary empty X has
no edge maps and the infimum is top; no exceptional nonempty-index assumption
is present. Universes are explicitly bound by `universe u`, and all simplicial
spaces are arbitrary in that universe; the indexing simplex category is small.
Fields, characteristic, schemes, and zero-object assumptions do not occur.

Independent searches (the prescribed wrapper appends searches.jsonl):

- LeanFinder: `Reedy fibrant bisimplicial object invertible morphisms zeroth
  horn restriction`; eight hits, about ordinary horns, Kan lifting and horn
  colimits, not this two-direction Segal-space statement.
- Loogle: `"horn", "IsWeakHomotopyEquivalence"`; no hits.
- Wrapper grep: `equivalenceMapping|outerHornInclusion|Rezk`; one unrelated
  Rezk citation in Mathlib's pushout-product lifting file.
- Direct rg on project lean/Sheaf, all upstream WeilConjectures, and Mathlib
  AlgebraicTopology using `invertible.*(horn|mapping)`, `equivalenceMapping`,
  `mappingEdgeEvaluation`, `uncurriedRowIso`, `outerHornInclusion`, `hoequiv`,
  and `outer.?horn`: no exact preexisting statement or general construction.
  Nearby outer-horn results are quasicategory filling criteria. I opened
  SegalInverseEvaluation.edgeEvaluation too: it evaluates only the distinguished
  edge of the WalkingIso nerve, not arbitrary F(1) -> X, and its mapping source
  is specialized. The general existing mappingSpace/mappingSpacePre are reused.

The three proof-only imported modules have the recorded signatures: arbitrary-base
strict fibrewise weak equivalence for two fibrations; the natural realization
cylinder homeomorphism with endpoints; and homotopy/basepoint-change invariance
of weak homotopy equivalences. The three Segal proof nodes without Lean records
remain the explicitly named future proof dependencies in the docstring, not
missing notions in this statement. The seven proof paragraphs agree step by
step with the node, including the base fibre calculation, the C(k) pushout,
the finite-face interval cover, the all-edge inverse-image argument, B(k),
and two-out-of-three. The d-zero face in the cover follows the proof of Rezk
11.11, as the node already specifies.

No new Lean or node mismatch was found in this round, so I preserved their
content. The earlier duplicate-mapping-space repair is already present and
was verified rather than repeated. I added this required, current second-reading
section; the Worker report and earlier reading remain intact. Every declaration
has a source/blueprint docstring; the only theorem is the named item with sorry.
All definitions contain actual data and only their necessary naturality and
membership proofs. No local notation, private copy, unbound binder, or overlong
Lean line was found. The node's lean.statement is verbatim its theorem signature.

Validation this reading: scompile.py compiled both the sandbox and named module
cleanly within the default 60-second limit (6.2 seconds each), no errors or
warnings. The delivery preflight and push results are recorded below when run.

Delivery dry run: deliver2.py --no-push returned OK at c0ac7d1b04:
preflight and compilation passed; nothing was pushed by the dry run.
