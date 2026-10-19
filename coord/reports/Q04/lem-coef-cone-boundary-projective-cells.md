## Worker report

Item: `lem-coef-cone-boundary-projective-cells`, Q04, stage 2, 2026-10-17.
Module: `Sheaf.AlgebraicTopology.ConeBoundaryProjectiveCells`.
Main declaration: `SSet.CoherentCone.cone_boundary_projective_cells`.
Only this theorem has `sorry`; no mathematical theorem is proved. The seven auxiliary
constructions have real data, and `PointFormula` packages the natural isomorphism and its
commuting squares. No construction is chosen from the final theorem.

Hypotheses and clauses, in node order:

- Small simplicial categories and simplicial sets in the chosen universe are `SCat.{u}` and
  `SSet.{u}`. Both object sets and mapping simplices of `SCat.{u}` are in `Type u`. Every
  universe and variable is bound explicitly. There is no Kan, quasicategory, monomorphism,
  cofibrancy or model-structure hypothesis.
- The coherent realization is the recorded `SSet.PinchedCube.rigidification`, applied to
  arbitrary `S` and `X`. The fixed functor is `a : rigidification.obj S ⟶ A`; the arbitrary
  object over `S` is `p : X ⟶ S`.
- The ordered last-vertex join is the recorded `Enhanced.rightJoinCone X`, with initial leg
  `Enhanced.rightJoinConeInclusion X` and final leg `Enhanced.orderedJoinInr X Δ[0]`.
  Its existing terminal-augmentation/convolution construction has the pure `X_r`, pure
  singleton and mixed `X_j` summands for `j < r`, in exactly the order in the node. It is
  used directly, not replaced by a topological cone or by a join of different variance.
- `moduleCategory a p` is the actual enriched pushout of `C[X] → C[X ⋆ Δ[0]]` and
  `C[p] ≫ a`. Mathlib lists the cone factor first; symmetry of the displayed pushout order
  changes no mathematical construction. `baseInclusion` and `coneInclusion` are its two
  canonical legs. `coneVertex` uses the coherent zero-simplex unit and the pure final leg.
- `value a p c` is precisely the mapping simplicial set from the image of `c` to that last
  vertex. `precomposition a p c d` uses the base map on the complete simplicial mapping set
  `A(d,c)`, followed by enriched composition. The first conjunction's existential `L`
  is an `EnrichedFunctor SSet Aᵒᵖ SSet.{u}`, with every object equal to `value` and every
  enriched map heterogeneously equal to the curry of this action. These normalizations
  specify all functor data; the existential only postpones the action laws. In particular,
  the assertion does not merely supply an unrelated functor or only vertexwise naturality.
- The full subcategory on `A` is expressed by `Function.Injective (baseInclusion a p).obj`
  and `IsIso ((baseInclusion a p).map c d)` for every `c,d`. The maps are the canonical
  inclusion maps, so they also respect identities and composition by their existing
  enriched-functor laws. Injectivity prevents different coefficient objects from being
  identified.
- Empty reverse mappings are `IsEmpty` in every simplicial degree for
  `hom (moduleCategory a p) (coneVertex a p) ((baseInclusion a p).obj c)`.
- Point endomorphisms are the displayed `Nonempty (... ≅ Δ[0])`. Since `Δ[0]` is terminal,
  its isomorphism, when it exists, is the unique terminal map and hence canonical/natural.
- A set `K` over a vertex `s` is `SSet.const (X := K) s`. The object `a(s)` is
  `coefficientVertex a s`, computed by the coherent zero-simplex inclusion followed by `a`.
- `PointFormula.iso` is the family
  `value a (SSet.const s) c ≅ hom A c (coefficientVertex a s) ⊗
   (SSet.stdSimplex.{u}.leftKanExtension qFunctor.{u}).obj K`.
  Tensor in `SSet` is the degreewise cartesian product. The left Kan extension is Mathlib's
  existing colimit/coend operation, not a new definition of the `Q` realization.
  `Functor.leftKanExtensionObjIsoColimit` identifies this value with the colimit of
  `CostructuredArrow.proj stdSimplex K ⋙ qFunctor`: objects are simplices of `K`, and arrows
  impose exactly `(K(α)z,q) ~ (z,Q(α)q)`. Thus all simplex operators, including degeneracies,
  are present. This matches both the node's quotient and HTT Remark the project server.
- `PointFormula.action` is the full simplicial precomposition square; the associator merely
  regroups `A(d,c) × (A(c,a(s)) × |K|_Q)` before composing the first two factors.
- The coend on `Δ[0]` has its canonical terminal map an isomorphism, stated with `IsIso`.
  The final clause gives the representable identification for `K = Δ[0]`. Together with
  `PointFormula.iso`, this is the same point specialization, not a new unrelated functor.
- `PointFormula.naturality` quantifies simultaneously over `f:K→K'`, `h:S→S'` and
  `F:A→A'` with `a ≫ F = C[h] ≫ a'`. The two pushout leg equations specify the unique
  induced cone functor `g`; it is not an arbitrary unconstrained map. The equalities
  `hc,hv,hs` record its endpoint transports and the image of `a(s)`. These are forced by
  those leg equations, the coherent zero-simplex unit and the compatibility of `a,a'`;
  they are not restrictions on the original `A,S,K` or on their maps. The equation compares
  the actual map on cone homs with `F` on the first factor and the coend functor on `f` on
  the second factor. Identity choices specialize it to naturality in each parameter.
  The canonical old-to-old mapping identifications are automatically natural by the base
  leg equation; the point endomorphism identification is natural by uniqueness of the
  terminal map. Every displayed identification is therefore accounted for.
- All joins, pushouts, mapping spaces, Kan extensions and products have values in the
  fixed universe `u`. Universes of indexing collections/functor types may be `u+1`, as
  usual; no mapping simplicial set or simplex set has been enlarged or excluded.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicTopology.PinchedCubeLatching`: `SSet.PinchedCube.coherentSimplex`,
  `sCatColimits`, `rigidification`, `coherentSimplexUnit`, `qFunctor`, `Q`, and
  `pinched_cube_latching`. I read the full construction, statement and proof docstring.
  In particular `qFunctor` uses every monotone map, and the recorded theorem identifies its
  quotient model canonically with `C[J^n](x,y)`.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `SSet.Enhanced.rightJoinCone` and
  `rightJoinConeInclusion`. I read their full signatures/docstrings and the underlying
  `orderedJoinFunctor` in `PushoutJoinSaturation` and both pure-factor inclusions in
  `JoinSliceRightFibration`. The landed owner `def-coef-infinity-relative-cone` was added
  to `stmt_deps` under the rule permitting added landed statement dependencies.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`: proof import, with the full
  `SSet.Bergner.simplicial_interval_lifting` signature/docstring inspected. Its small
  cocompleteness clause is already used by `PinchedCube.sCatColimits`.
- Mathlib: `EnrichedFunctor`, `eComp`, `MonoidalClosed.curry`, enriched opposite,
  `pushout`/`pushout.inl`/`pushout.inr`, `Functor.leftKanExtension`,
  `Functor.leftKanExtensionObjIsoColimit`, and the simplicial terminal zero-simplex.

Edge cases checked mathematically before writing: `X = ∅` keeps all of `A` and the new
vertex; `K = ∅` has empty coend and no old-to-new arrows; `K = Δ[0]` has coend `Q^0 = Δ[0]`;
`K = Δ[1]` has coend `Q^1`; empty `A` and empty `S` are allowed, with vertex-dependent
clauses vacuous exactly when no vertex exists; a coefficient functor identifying vertices
or arrows is allowed. Nontrivial endomorphisms in a one-object `A` are retained by the
fullness clause. All mapping-space naturality is simplicial, not just degree zero.

Searches (actual msearch calls are logged in sandbox `searches.jsonl`):

1. `msearch.py ... leanfinder "Free coherent cone collage has unchanged base hom spaces
   and point straightening is representable times pinched Q realization"`: eight generic
   cone/raise-cone hits (`CostructuredArrow.CreatesConnected.raiseCone_pt`, etc.), no coherent
   enriched collage or point formula.
2. `msearch.py ... loogle "CategoryTheory.EnrichedFunctor, CategoryTheory.Limits.pushout"`:
   zero hits.
3. `msearch.py ... grep "conePushout|qRealization|[Cc]ollage|[Ss]traightening"`: eight
   generic pushout-colimit comparison hits in Mathlib, no exact statement.
4. `rg` of upstream `WeilConjectures` for the same expression, and for this item id:
   no hits. The name check in Mathlib, upstream, `dag/lean_names_upstream.json` and
   `lean/Sheaf` found no `SSet.CoherentCone` declaration or main theorem name.
5. `rg` of `lean/Sheaf` found `UnmarkedStraighteningQuillen`'s explicit quotient realization
   and its opposite-coefficient pushout, and `RightStraighteningFiberComparison`'s
   realized-base specialization. Neither states this node's arbitrary-coefficient
   collage/point formula. Both are downstream in the complete DAG: importing either
   creates `unmarked-straightening-quillen → simplicial-right-fibration-presentation →
   cone-boundary-projective-cells`. Accordingly no downstream module is imported and no
   duplicate quotient or enriched-diagram API is introduced. The arbitrary-`A` pushout
   is written directly using Mathlib; its existing specializations can later be related
   by pushout uniqueness. The coend uses Mathlib's general Kan operation directly.
6. The existing join, coherent realization and pinched `Q` were found and reused, as
   detailed above. No missing independent notion or unusable dependency was found.

Source check: opened [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), printed
pp. 73–76, Sections 2.2.1–2.2.2. The correspondence on p. 73 is the same pushout with
`A = Cᵒᵖ`; Remark the project server on p. 75 identifies the left Kan extension with the coend;
p. 76 defines `J` and `Q`. The module docstring carries the node's seven-step proof plan.
There is no statement correction and no disputed clause. No new nodes or dependency repairs.

Validation: `scompile.py Q04 lem-coef-cone-boundary-projective-cells
lean/Sheaf/AlgebraicTopology/ConeBoundaryProjectiveCells.lean` passed both single-file
sandbox/library checks cleanly (1.7 s each). The first trial exposed an implicit universe-0
choice in `stdSimplex`; all Kan-extension occurrences now explicitly use universe `u`.

## Second reading by Q04

Independent second reader, 2026-10-17. I opened the original and sandbox node,
its seven proof steps, the whole delivered Lean module, and the recorded dependency
signatures. I read HTT Sections 2.2.1--2.2.2 online (printed pp. 73--76): the
correspondence uses the same right cone and coefficient category, and the
cosimplicial extension in Remark the project server is the displayed coend. There is no
ambient Kan, quasicategory, injectivity, characteristic, or model-category
hypothesis on this construction. The cited source is HTT, not a Stacks tag.

My object/hypothesis/conclusion inventory and comparison, in node order:

1. Chosen small universe; arbitrary simplicial category A and simplicial sets S,X;
   a:C[S]→A and p:X→S. Lean: `universe u`, `SCat.{u}`, `SSet.{u}`,
   `a : rigidification.obj S ⟶ A`, `p : X ⟶ S`. Verdict: exact. I opened
   `CoherentNerveInfrastructure`: SCat bundles object types in Type u and mapping
   objects in SSet u, with arbitrary enriched object functions as morphisms.
   There is no hidden locally-Kan or coefficient restriction.
2. Ordered last-vertex join with pure X, pure point and mixed initial X blocks.
   Lean: `Enhanced.rightJoinCone X`, `rightJoinConeInclusion X` and
   `orderedJoinInr X Δ[0]`. Verdict: exact. I read their definitions in
   `RelativeInfinityCone` and `JoinSliceRightFibration`, and the terminally
   augmented convolution `orderedJoinFunctor` in `PushoutJoinSaturation`.
   Its degree-r normal form has precisely the node's summands, including r=0.
3. The actual pushout M_p and its new vertex v. Lean: `moduleCategory a p`,
   `baseInclusion`, `coneInclusion`, `coneVertex`. Verdict: exact. The cone
   factor is the first Mathlib pushout leg; the other leg is C[p] followed by a.
   The vertex is the pure final zero-simplex, mapped by the coherent simplex unit.
4. L_a(X)(c)=M_p(c,v), with precomposition action and enriched presheaf laws.
   Lean: `value`, `precomposition`, and the first conjunction's existential L.
   Verdict: exact. Object equalities fix all values; HEq fixes every enriched map
   to the curry of precomposition. The braiding puts the tensor factors into
   curry's order. The existential postpones the functor laws, with no unidentified
   action data and no reduction to naturality on vertices.
5. The old full category is A. Lean: injectivity of `baseInclusion.obj` and
   `IsIso ((baseInclusion a p).map c d)` for all c,d. Verdict: exact. These are
   the canonical enriched inclusion maps, which already preserve composition
   and identities; the statement does not replace fullness with a DK equivalence.
6. M_p(v,c) empty and M_p(v,v) a point. Lean: `IsEmpty` in every simplex degree
   and `Nonempty (... ≅ Δ[0])`. Verdict: exact. The latter identification is
   canonical because Δ[0] is terminal. No choice of reverse arrow is introduced.
7. Arbitrary K over a vertex s and coefficient object a(s). Lean:
   `SSet.const (X := K) s` and `coefficientVertex a s`. Verdict: exact. I read
   Mathlib's constant simplicial map; its degeneracies implement the map through
   that vertex. The coherent zero-simplex unit identifies the appropriate object.
8. Natural isomorphism with A(c,a(s)) times the Q-realization. Lean:
   `PointFormula.iso` and the SSet tensor with
   `(SSet.stdSimplex.{u}.leftKanExtension qFunctor.{u}).obj K`.
   Verdict: exact. The tensor is cartesian. I opened Mathlib's
   `Functor.leftKanExtensionObjIsoColimit`: its costructured-arrow category is
   the simplex category of K, so its colimit imposes exactly the stated coend
   relations for every monotone operator. The explicit universe annotations
   prevent the earlier universe-zero specialization.
9. Naturality in c and all displayed parameter identifications. Lean:
   `PointFormula.action` and `PointFormula.naturality`. Verdict: exact.
   Action uses complete simplicial hom objects. The parameter square covers
   f:K→K', h:S→S', F:A→A' with a≫F=C[h]≫a'. The two leg equalities uniquely
   prescribe g; hc,hv,hs merely transport the forced endpoints, and do not
   restrict the original parameters. Fullness comparisons commute by the base
   leg equality, and point endomorphism comparisons by terminal uniqueness.
10. At K=Δ[0], the representable. Lean: `IsIso` of the Q-realization's unique
    terminal map, together with the final representable-isomorphism clause.
    Verdict: exact. Applying PointFormula at Δ[0] and this terminal isomorphism
    gives the natural representable specialization, so the final existential
    isomorphism clause does not lose its compatibility with the earlier formula.
11. Smallness. Lean: every construction returns SCat u or SSet u, and u is
    arbitrary. Verdict: exact. Index/family collections may lie in the next
    universe; simplex sets and constructed mapping objects remain in u.

Edge cases: X empty retains A and the pure cone vertex; K empty has an empty
simplex-indexed coend and empty forward mapping sets. At K=Δ[0] the coend is Q^0;
at K=Δ[1] it is Q^1. Degree zero of the join has exactly its two pure summands.
A and S may be empty; the s-clauses are then vacuous only when no vertex exists.
Noninjective a and coefficient categories with nontrivial endomorphisms are
allowed. No scheme, ring, characteristic, nonemptiness or finiteness hypothesis
belongs to this node. All universes are explicitly bound; no equality of distinct
site universes is relevant here.

Independent searches, with different queries from the author (msearch calls
recorded in searches.jsonl):

- LeanFinder: `Simplicial enriched category free terminal-object attachment
  represents maps by a cosimplicial coend tensor`. Eight hits, including
  `SimplicialCategory.sHom`, `SimplicialThickening.functor`, ordinal inclusions
  and `SimplicialNerve`; their signatures do not state this pushout calculation.
- Loogle: `CategoryTheory.EnrichedFunctor, SSet`. Three hits, precisely
  `SimplicialThickening.functor`, `functor_id`, `functor_comp`; no match.
- Grep via msearch: `terminalAttachment|coneModule|[Rr]igidification|[Pp]inched[Cc]ube`.
  Zero hits. Direct rg of upstream WeilConjectures, Mathlib and
  dag/lean_names_upstream.json finds only unrelated geometric rigidifications.
- Direct rg of project Sheaf sources finds the recorded PinchedCube and join
  infrastructure and downstream `UnmarkedStraighteningQuillen` and
  `RightStraighteningFiberComparison`. I opened their cone/value signatures:
  the former takes an opposite coefficient category, the latter specializes the
  base. Neither states the present arbitrary-A theorem. Importing their
  downstream constructions would close a dependency cycle. The present module
  reuses the existing underlying pushout/Kan-extension operations, rather than
  creating another quotient model or diagram category.

I verified the recorded `pinched_cube_latching` signature, including its
normalized canonical isomorphisms, all monotone operators and Q^0. I also read
`simplicial_interval_lifting`'s cocompleteness clause, which supplies the recorded
sCatColimits instance. The added statement dependency is the already recorded
owner `def-coef-infinity-relative-cone`; no new definition node or dependency
module is delivered. There is no statement_change and no citer audit is required.

H5--H9: all seven helper constructions have real data from the canonical
operations. The PointFormula structure only records the requested witnesses.
The final theorem is the only sorry, its docstring carries all seven node proof
steps with the appropriate dependencies, all declarations have source/blueprint
docstrings, there is no private notation or instance, and all lines are at most
100 characters. I checked the node's lean.statement byte-for-byte against the
file signature: equal. The natural-language node statement is unchanged; only
lean and the authorized added statement dependency differ from the shared node.

Mismatches found: none. Changes made by this reading: this audit report only;
the correct Lean and node record are preserved. Required validation:
`scompile.py Q04 lem-coef-cone-boundary-projective-cells
lean/Sheaf/AlgebraicTopology/ConeBoundaryProjectiveCells.lean` passed both
sandbox and library single-file checks, without errors or warnings (1.8 s and
2.0 s respectively).
