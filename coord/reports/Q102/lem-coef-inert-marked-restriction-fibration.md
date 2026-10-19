## Worker report

The module `Sheaf.CategoryTheory.InertMarkedRestrictionFibration` states
`SSet.Enhanced.inert_marked_restriction_fibration`, with its main proof postponed by `sorry`. The maintainer replacement also postpones
the named well-definedness obligation for marked restriction; see the second reading below.
Its three helpers define the specified marked-vertex predicate, full marked subcategory,
and actual simplicial restriction. Definitions have real data and use no choice of a lift.
No statement correction, new node, or dependency repair is needed.

The previous attempt confused the reviewed Q77 stage-1 split with a stage-2 statement:
the current item has no Lean record. Its stage-1 statement and six-step proof are retained.
The current blueprint is main-20261015; the historical parent is the finite-level adjunction
comparison in `prop-coef-integral-exceptional-adjoint.proof.md`. This delivery formalizes its
already split supporting lemma, without changing the blueprint route.

Hypothesis and clause correspondence:

- Small simplicial sets: `{K E P : SSet.{u}}`, with explicit arbitrary universe `u`.
  There is no quasicategory hypothesis on the indexing simplicial sets K or A.
- Categorical fibration of quasicategories: `(r : E ⟶ P) (hr : IsIsofibration r)`.
  The existing predicate includes `Quasicategory E`, `Quasicategory P`, inner horn
  lifting, and lifting of equivalence edges with prescribed source and exact image.
- Simplicial subset: `(A : K.Subcomplex)` with its actual inclusion `A.ι`.
- Fixed base diagram: `(f : K ⟶ P)`; its restriction is literally `A.ι ≫ f`.
- Marked edges and all degenerate edges marked: `(M : Set (K _⦋1⦌))` and
  `(hM : ∀ x : K _⦋0⦌, K.σ 0 x ∈ M)`.
- Inherited marking: `(A.ι.app _) ⁻¹' M`, exactly the edges of A belonging to M.
- Unmarked lift simplices: the existing `sectionCategory r f` is the degreewise
  fiber of postcomposition by r over `diagramVertex f`. In degree d its internal-hom
  coordinate is a map K × Δ[d] → E whose whole image in P is f composed with projection.
  The Δ[0] coordinate contributes exactly one simplex in each degree. Simplicial
  operators restrict this whole family; no condition is imposed only at vertices.
- Marked vertices: `IsMarkedSection r f M H` requires, for every `m ∈ M`,
  `IsCocartesianEdge r (SSet.yonedaEquiv.symm m ≫ sectionUnderlying H)`.
  Thus the precise image of each marked edge is tested using the dependency's horn predicate.
- Full marked lift category: `markedSectionSubcomplex r f M` is the existing
  `fullSubcomplex` on that vertex predicate. It retains every simplex having marked vertices.
- Restriction: `markedSectionRestriction r f M A` applies the existing
  `sectionRestriction A.ι r f` in every degree and packages its image in the target full subset.
  Naturality and the pullback projection equation identify underlying vertices with literal
  precomposition by A.ι; the parameter simplex and fixed base coordinate remain unchanged.
- Both marked categories are quasicategories and restriction is a categorical fibration:
  `IsIsofibration (markedSectionRestriction r f M A)` includes both quasicategory
  conditions and the required inner-horn and specified-source equivalence lifts.
- Closure under equivalence in the unmarked category: the second conjunct quantifies
  over every `e : (sectionCategory r f) _⦋1⦌`, assumes `IsEquivalenceEdge` there and
  markedness of its source (`δ 1`), and concludes markedness of its target (`δ 0`).
  This universal statement also applies with K replaced by A and the inherited marking
  (take the whole subcomplex as the otherwise arbitrary subset parameter).
- Transformations and all higher simplices over the identity are retained by the strict
  fiber and full-subcomplex definitions. No invertibility condition is imposed on ordinary
  transformations. No existence of marked lifts, other cocartesian lifts, Segal conditions,
  or approximation hypothesis occurs in any binder or helper.

Dependency declarations used (all in namespace `SSet.Enhanced` unless indicated):

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`, `IsEquivalenceEdge`,
  `diagramVertex`, together with Mathlib `SSet`, `Subcomplex`, and the internal hom.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`: `IsIsofibration`; its
  `isofibration_exponentiation` and `exponentialCorner` are the proof's corner-map input.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` publicly reexports
  `Sheaf.CategoryTheory.InfinityFibrations`: `IsCocartesianEdge` and `fiber`.
  The newer `cocartesianFibrationOver` record is not misused to assume existence of lifts.
- `Sheaf.CategoryTheory.CocartesianSectionColimits`: `sectionCategory`, `sectionUnderlying`.
- `Sheaf.CategoryTheory.RelativeRightKanRestriction`: `sectionRestriction`. It has no
  full-subcategory or quasicategory restriction on its domain parameter, so is usable here.
- Proof imports are `InnerFibrationEquivalenceOuterHornLift.inner_fibration_equivalence_outer_horn_lift`,
  `EquivalenceOuterHornFilling.equivalence_iff_outer_horn_filling`,
  `PointwiseEquivalences.pointwise_equivalences`, and
  `InfinityCocartesianCompositionInitiality.cocartesian_composition_initiality`,
  where each prefix before the last dot abbreviates its `Sheaf.CategoryTheory` module.

Added the two already landed owning nodes `lem-coef-cocartesian-section-colimits` and
`lem-coef-relative-right-kan-restriction` to `stmt_deps` to cite the reused generic helpers.
This is the authorized addition of landed statement dependencies, not a copied notion.
All other node fields are unchanged, including source, proof and status.

Edge cases checked mathematically before writing:

- A = K gives identity restriction; A empty gives restriction to the terminal empty-diagram
  lift category. K empty likewise gives the terminal category without nonemptiness assumptions.
- E empty is allowed. If there is no marked lift, the source category may be empty; the
  categorical lifting requirements prescribe an existing source object and do not assert one.
- For E = N([1]) over a point, marking the nonidentity arrow of K = Δ[1] restricts to
  edge-inverting diagrams, so arbitrary diagrams are not erroneously claimed marked.
- With r the identity, all edges are r-cocartesian and the unique fixed-base lift remains.
- With only degenerate edges marked, every vertex satisfies the condition; degenerate images
  are cocartesian for an inner fibration. The inherited marking includes all degeneracies.
- Empty marking is allowed precisely when there are no vertices; no such case is excluded.
- The face convention δ 1 = source and δ 0 = target agrees with `IsIsofibration`.

Searches (through the prescribed msearch wrapper, and direct read-only ripgrep):

- LeanFinder: "Restriction of coherent lifts preserving cocartesian marked edges along a
  simplicial subset is a categorical fibration of quasicategories": eight hits, primarily
  Quillen all-horn fibration infrastructure and `SSet.Subcomplex.lift`; none states the result.
- Loogle: `SSet.InnerFibration, SSet.Subcomplex`: zero hits.
- Mathlib grep: `marked.*[Rr]estrict|[Ll]ift.*[Cc]ocartesian|[Ii]sofibration`, subdirectory
  AlgebraicTopology: zero hits. The Quillen fibration hits require all horns and are not
  categorical isofibrations. The ordinary-category cocartesian predicates are a different notion.
- LeanSearch: "A full subcategory of coherent lifts preserving selected cocartesian edges is
  replete under equivalence and restriction is an isofibration": eight hits, on ordinary-category
  full subcategories, ordinary cocartesian arrows, and model-category weak equivalences; no match.
- Upstream grep of the exact node id and marked-lift/restriction names found no declaration.
  The only general marked/lift textual hit was an unrelated projective-space diagram caption.
- Project grep found existing `sectionCategory`/`sectionUnderlying` and `sectionRestriction`,
  reused here. `operadicSections` is specialized to inert arrows over FinStar; it does not
  express arbitrary markings. `cocartesianSections` constrains every edge of an identity-base
  section; it does not express this marking or restriction theorem. No existing declaration
  matches the item, and all four new full declaration names were absent in project, upstream,
  Mathlib, and the upstream-name index.

Sources checked: Kerodon 01F1 (exponential corner), 01DK (componentwise equivalences),
and 01H0 (relative outer-horn lifting) were opened online. The existing DAG proof supplies
its full marked refinement via the cocartesian composition/cancellation theorem. The module
carries all six proof steps, including the strict-fiber equivalence check and both naturality
triangles. No disputed statement was found.

Source metadata observation: `source.place` names the dual of HTT Proposition 2.4.4.3
(the mapping-space characterization). The actual six-step proof and module use the dual
of HTT Proposition 2.4.1.7 (composition and cancellation), together with Kerodon 01DK,
01H0 and 019F. The mapping-space characterization can also establish the needed invariance;
this is a citation-route discrepancy, not a different mathematical statement. The source
field is outside the permitted stage-2 delta and is preserved.

Validation: `scompile.py` accepted both its sandbox compile (32.6 s) and its library-path
compile (23.1 s), with no errors or warnings. The sole theorem has its intended `sorry`
proof. The delivery preflight and its additional compile are run through
`deliver2.py --no-push` before the final push.

## Second reading by Q102

Independent maintainer second reading, 2026-10-17, of immutable delivery
93ea3507fcba40c56547ac88922f1560ee2353d0. This replaces the delivered placeholder;
it does not claim that a worker performed a second reading. Verdict: FIX, with the
complete module, Lean record, and report replacements supplied by the maintainer.

I read the packet, check-brief2.md in full, the snapshot item and all five statement
dependency nodes, the delivered module and report, and the exact dependency declarations
in the read-only Q102 clone. I opened Kerodon 01F1, 01DK, 01H0 and HTT online.

Hypotheses and conclusions checked individually:

- Arbitrary small K, E, P: `{K E P : SSet.{u}}`, arbitrary explicitly bound u.
  There is no quasicategory restriction on K or A. A common sufficiently large universe
  is the established enhanced-diagram convention; no equality of distinct site universes
  or finiteness restriction has been introduced.
- Categorical fibration r: `IsIsofibration r` includes quasicategories E and P,
  `InnerFibration r`, and exact outgoing equivalence lifts with prescribed source.
  No assumption of a cocartesian fibration or of all cocartesian lifts is present.
- Simplicial subset A: `K.Subcomplex`, with its actual degreewise injective `A.ι`.
  Fixed diagram f is arbitrary. Its target restriction is literally `A.ι ≫ f`.
- Marking M is a set of one-simplices; hM marks every degeneracy of a vertex.
  The target uses `(A.ι.app _) ⁻¹' M`, exactly the inherited marking, including
  inherited degenerate edges by naturality of the inclusion.
- `sectionCategory r f` is the existing `fiber ((ihom K).map r) (diagramVertex f)`.
  The pullback fixes postcomposition on each entire parameter simplex, not merely
  on vertices. The terminal Delta[0] coordinate adds no choice of diagram or data.
- `sectionUnderlying` extracts the represented map K to E by the existing internal-hom
  equivalence. `IsMarkedSection` tests the represented image of each edge in M using
  the existing relative initial-outer-horn predicate `IsCocartesianEdge`.
- `markedSectionSubcomplex` uses the recorded `fullSubcomplex`, retaining precisely
  the simplices all of whose vertices satisfy that predicate. It imposes no condition
  on the invertibility of transformations or on horizontal parameter edges.
- `markedSectionRestriction` retains the actual `sectionRestriction A.ι r f` as its
  underlying map in every degree. Its well-definedness uses only precomposition and
  the inherited marking; it assumes neither horn lifting nor existence of a marked lift.
- The first main conjunct is `IsIsofibration` of that very restriction. Its first two
  conjuncts give both marked categories' quasicategory conditions; its remaining
  conjuncts give inner lifting and exact specified-source equivalence lifting.
- The second main conjunct quantifies over equivalence edges of the unmarked strict
  fiber and carries markedness of `δ 1` (source) to `δ 0` (target). This is repleteness
  over the identity of f. The same theorem with K replaced by A gives the analogous
  assertion on A; no separate nonemptiness assumption is needed.
- All transformations and higher simplices stay over f or its restriction by the strict
  fiber construction. There are no operadic, approximation, Segal, completeness, or
  extra cocartesian-lift assumptions hidden in any binder.

Dependency and proof check:

`IsEquivalenceEdge` supplies an inverse and both inverse triangles. `fullSubcomplex`
uses every vertex, and the internal hom is Mathlib's coherent functor simplicial set.
`IsIsofibration` uses the stipulated source convention. `InfinityFibrationsOverSimplicialBases`
publicly reexports `InfinityFibrations.IsCocartesianEdge`; its more general fibration
predicate is not assumed here. The generic `sectionCategory`, `sectionUnderlying` and
`sectionRestriction` have no extra quasicategory or existence binders. The two added
statement dependencies own these helpers; they are landed and do not import this item.

All six proof steps are sound. The unmarked restriction is the strict pullback of the
01F1 exponential corner. Relative outer-horn lifting over a constant base simplex,
followed by the outer-horn converse, recognizes its lifted equivalences inside the
strict fiber. Pointwise equivalences and relative initial-horn lifting make each
component r-cocartesian. In the naturality square the triangle with H(m) and the target
component makes the diagonal cocartesian. The other triangle cancels the source
component to show H'(m) cocartesian, using precisely the first conjunct of
`cocartesian_composition_initiality`. Fullness retains inner fillers and all equivalence
witnesses. Every required proof module is imported, with statement dependencies public.

Edge cases: A=K; A empty; K empty; empty E or empty strict fibers; no marked lifts;
r=id; base a point; only degenerate edges marked; marking all edges. The empty diagram
category is terminal, but the source need not be inhabited. For E=N([1]) over a point
and K=Delta[1] marked on all edges, only edge-inverting diagrams belong to the full
marked subset, as intended. No zero-dimensional lifting/surjectivity claim is added.

One-definition searches: independent ripgrep over Q102 lean/Sheaf, upstream
WeilConjectures, the upstream-name index, and Mathlib AlgebraicTopology found no exact
existing item. I inspected `operadicSections` (inert edges over FinStar), `markedFunctors`
and `markedRestriction` (fixed monoidal-simplex base), `cocartesianSections` (all edges
and identity base), and `SSet.Marked.Over.cartesianFunctors`/`functorRestriction`
(generic marking-preserving maps in a different marked-over presentation). None gives
this declaration on the recorded strict section fiber, with arbitrary r, f and M.
The delivery reuses the existing full-subcomplex, fiber, edge and restriction notions.
Mathlib's ordinary-category cocartesian predicates and Quillen all-horn fibrations
are different notions. The worker's LeanSearch/LeanFinder/Loogle records were also read.

Findings and repairs:

1. H11: the delivered second-reading section explicitly said no reading occurred.
   Replaced it with this actual independent clause-by-clause reading.
2. H6/stage-2 well-definedness convention: the delivered map included a local proof
   of its marked-subcomplex membership, including the pullback/underlying-map equality.
   Extracted this obligation into the named theorem
   `sectionRestriction_mem_markedSectionSubcomplex`, with source/blueprint and a complete
   proof plan and `sorry`. It is the node's restriction well-definedness clause, not a new
   mathematical prerequisite. The map still has the same explicitly constructed data;
   only its Prop-valued membership certificate is deferred. Naturality remains the
   structural equality inherited from the existing restriction. Both theorem bodies
   are now exactly `by sorry`; no new result is proved locally.
3. Added the required main-definition/main-statement lists to the module docstring.
   Recorded the new helper in `lean.declarations`. All declarations have source and
   blueprint docstrings, and the main theorem keeps all six proof steps.
4. Replaced the report's garbled HTT citation note with the accurate distinction
   above. The source metadata itself and the mathematical node statement are preserved.

Validation: the original main signature is byte-for-byte equal to `lean.statement`.
The replacement keeps that exact signature and changes only the declaration list and
explanatory note in the Lean record. There are no unbound variables, overlong lines,
hollow definitions, arbitrary maps, or data selected from a postponed existence theorem.
No statement_change, dependency repair, new DAG node, or citer audit is required.

I reproduced the original per-file compile using the prescribed scompile.py on the
snapshot module: exit 0, sandbox 1.8 s, library path 1.8 s, no diagnostics. I also
compiled the complete fixed module under its actual Sheaf/CategoryTheory module path:
exit 0, sandbox 1.6 s, library path 1.8 s, no diagnostics. The current scompile.py
forwards to the server overlay and wire confirmation; its returned evidence reports
private /dev/shm overlay artifacts. No global build or direct ssh was run, and no
snapshot, branch head, project clone, or live Lean file was changed.
