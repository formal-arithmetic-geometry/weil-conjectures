## Worker report

This is a stage-2 statement delivery, not a repeated stage-1 split. The retained
sandbox initially contained only dispatcher markers. The current shared node has an
accepted eight-step split, but no `lean` attachment. The earlier worker's unchanged-node
rejection concerned the split; this delivery supplies a new Lean record and theorem.

The module `Sheaf.CategoryTheory.InfinityDirectedConeCover` states
`SSet.Enhanced.exists_cofinal_of_directed_cone_cover`, with `sorry` as its only proof.
Its docstring carries all eight proof steps, including the two unstated decomposition
ingredients. No definitions, axioms, or additional postponed theorems are introduced.
The mathematical statement, proof, and proof dependencies of the node are unchanged.

Hypothesis and clause correspondence:

- The small quasicategory K is `(K : SSet.{u}) [Quasicategory K]`.
- The small nonempty partially ordered set is `(A : Type u) [PartialOrder A]
  [Nonempty A]`. The binder `hA` asserts an upper bound for every `Finset A`,
  including the empty finite set, exactly as the node requests.
- The simplicial subsets are `B : A → K.Subcomplex`. `hB : Monotone B` is
  increasing inclusion, and `hcover : iSup B = ⊤` is their degreewise union being K.
- The small simplicial bases are `L : A → SSet.{u}`. The supplied isomorphisms
  `e a : orderedJoinFunctor.obj (L a, Δ[0]) ≅ (B a).toSSet` are data, not merely
  existence or a stronger categorical terminal-object hypothesis. No quasicategory
  instance is imposed on `B a` or `L a`.
- The right cone is the existing ordered simplicial join with the zero-simplex.
  Its new vertex is `orderedJoinInr (L a) Δ[0]` applied to
  `stdSimplex.obj₀Equiv.symm 0`. Applying `(e a).hom` and then `(B a).ι` gives
  the exact specified cone vertex `t_a` in K.
- `∃ j : nerve A ⟶ K` supplies a single simplicial map before any target E or
  diagram H is chosen. `ComposableArrows.mk₀ a` is the vertex a of the ordinary
  nerve. The first conjunct says exactly `j(a) = t_a` with the preceding formula.
- `∀ (E : SSet.{u}) [Quasicategory E] (H : K ⟶ E)` quantifies over coherent
  target categories and diagrams in the fixed simplicial universe of the dependency.
  Universes and variables are explicit and `autoImplicit` is disabled.
- `c : (coconeCategory H) _⦋0⦌` is each supplied coherent cocone, with its full
  transformation and apex. The conclusion is the equivalence between
  `IsColimiting H c` and `IsColimiting (j ≫ H)` of its actual restriction.
- The restricted cocone is precisely `(gluingCoconeRestrict j H).app (op ⦋0⦌) c`.
  Reading that definition shows that it keeps the apex coordinate literally and
  applies internal-hom precomposition to the entire arrow coordinate, in every
  degree. Thus it retains the specified legs and all their compatibility simplices.
  This is the canonical comparison, rather than an existential replacement cocone.
  Naturality in H is built into this actual precomposition: on any simplex of
  `Fun(K,E)` it restricts the K-coordinate along j. No additional choice of a
  comparison depending on H occurs, so coherent transformations and higher
  simplices are restricted by the same map. The theorem is about that fixed map.
- There is no cocompleteness or colimit-existence hypothesis on K or E. The only
  colimit predicates concern the one supplied cocone and its restriction.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.coconeCategory`,
  `SSet.Enhanced.IsColimiting`, and their underlying comma and mapping-space
  definitions. The recorded dependency's full signatures and docstrings were read.
  Mathlib supplies `SSet.Quasicategory`, `CategoryTheory.nerve`,
  `CategoryTheory.ComposableArrows.mk₀`, and `SSet.Subcomplex`.
- `Sheaf.AlgebraicTopology.PushoutJoinSaturation`:
  `SSet.Enhanced.orderedJoinFunctor`. Its terminal augmentation and convolution
  definition give the ordered join, including the pure blocks.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`:
  `SSet.Enhanced.orderedJoinInr`, the genuine pure-right-block inclusion, built from
  the empty augmented simplex and the convolution generator.
- `Sheaf.CategoryTheory.InfinityColimitGluing`:
  `SSet.Enhanced.gluingCoconeRestrict`. Its full construction and endpoint checks
  were read; this exact existing declaration supplies restriction.
- The last three declarations' already landed owner nodes are added to `stmt_deps`
  under brief-stage2 §5, STMT_DEPS MAY GAIN LANDED NODES. No new node is needed.
- The already stated proof dependencies are imported non-publicly:
  `Sheaf.CategoryTheory.ConeMonoRightAnodyne`,
  `Sheaf.AlgebraicTopology.AnodyneCocones`, and
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`.
  The two decomposition proof dependencies currently have no Lean record, so their
  modules cannot be imported; they are named in the complete natural-language plan.
  They are not needed to type this statement.

Edge cases checked before drafting: an empty A is excluded exactly by the node;
nonemptiness and the cone presentations also exclude empty K. Empty `L a` is
allowed and gives a point cone. A singleton A gives selection of the supplied apex
of its single cone, with the usual colimit test. Repeated vertices and chains in
A are retained as degeneracies by `nerve A`. Non-quasicategorical bases and
subsets are permitted without any additional instance. Empty E produces no H
from the necessarily inhabited K; no artificial nonemptiness is imposed on E.
Overlapping cones and repeated apex vertices are permitted. Finite upper bounds
need not be chosen or monotone. No equality of unrelated universes is imposed.

Searches made, with actual output retained in `searches.jsonl`:

- `msearch.py leanfinder`: "A directed cover of a quasicategory by simplicial right
  cones admits a cofinal map from the nerve of the directed poset with the
  specified cone vertices". Eight hits concerned strict-Segal right Kan
  extensions, ordinary cocones, scheme covers, and subcomplex colimits; no match.
- `msearch.py loogle`: `SSet, cofinal`. Zero hits; the service also reported the
  unknown identifier `cofinal`. This alone is not evidence of absence.
- `msearch.py grep`: `cofinal|Cofinal|directed` in
  `AlgebraicTopology/Quasicategory`. Zero hits.
- `msearch.py leansearch`: "A directed union of simplicial right cones in a
  quasicategory has a cofinal map from the nerve of its indexing partially ordered
  set". Eight hits included the nerve/quasicategory definitions and scheme-gluing
  material; none states the directed-cone-cover assertion.
- `rg` searched upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for directed-cone/cofinal terminology and the
  exact item id. No exact statement was found. A separate collision search for
  `exists_cofinal_of_directed_cone_cover` in Mathlib, upstream, shared Lean, and
  upstream declaration names found no existing declaration.
- Searches of the shared Lean for cocone restriction and ordered join inclusions
  found the owning declarations above, which are reused without private copies.

The HTT source was read online at its recorded URL: Proposition the project server and its
retraction construction on printed pp. 383–384, PDF pages 400–401. The supplied
node is its literal-right-cone special case, with its more explicit prescribed
vertices and cocone test. There is no statement correction, dependency interface
repair, statement dispute, or mathematical fault to report.

Validation: `scompile.py NP lem-coef-infinity-directed-cone-cover` compiled the
module cleanly, including both the sandbox check and its library-path check.
The initial drafting error was a missing pair of parentheses in a vertex
projection; it was repaired using the actual subset inclusion `(B a).ι`.
The final theorem contains only `sorry` as required by stage 2.

## Second reading by NP

I independently read the shared node, the sandbox node and theorem, the four
statement-dependency records and the source of their declarations. The source is
HTT, not Stacks: [Proposition the project server, proof, printed pp. 383–384](https://www.math.ias.edu/~lurie/papers/highertopoi.pdf)
(PDF pages 400–401). Its retraction argument selects the specified final vertices
in a directed subset cover. The node explicitly specializes the local structures
to actual right cones and supplies an eight-step argument for that specialization;
it does not assert the whole proposition about constructing a poset from an
arbitrary κ-filtered category. The κ-filtered-category and cardinal hypotheses used
to construct the cover in the proposition are therefore not extra hypotheses of
this already-given-cover lemma. I checked the local extra-degeneracy construction:
appending the last cone vertex respects faces, and repeated appending is exactly
the corresponding degeneracy, even when different cone presentations are unrelated.

My object/hypothesis/conclusion checklist, in the node's order:

| Node clause | Lean rendering and verdict |
| --- | --- |
| Small quasicategory K | `(K : SSet.{u}) [Quasicategory K]`: exact Mathlib notion; no extra properties. |
| Small nonempty partially ordered A | `(A : Type u) [PartialOrder A] [Nonempty A]`: exact; its ordinary poset category is inferred, not an extra chosen category. |
| Every finite subset has an upper bound | `hA : ∀ s : Finset A, ∃ b : A, ∀ a ∈ s, a ≤ b`: exact, including the empty finite subset. No upper-bound choices or linear order are required. |
| Simplicial subsets K_a of K | `B : A → K.Subcomplex`: exact degreewise subsets stable under all simplicial operators. |
| Increasing family | `hB : Monotone B`: exact inclusion for a ≤ b. |
| Union is all of K | `hcover : iSup B = ⊤`: exact degreewise union, with no disjointness requirement. |
| Small bases and supplied right-cone presentations | `L : A → SSet.{u}` and `e : ∀ a, orderedJoinFunctor.obj (L a, Δ[0]) ≅ (B a).toSSet`: exact simplicial isomorphisms, with neither L_a nor K_a assumed quasicategorical. |
| Prescribed vertex t_a | The pure-right inclusion `orderedJoinInr (L a) Δ[0]` applied to `stdSimplex.obj₀Equiv.symm 0`, followed by `(e a).hom` and `(B a).ι`: exactly the specified cone vertex in K. The equality uses the actual nerve vertex `ComposableArrows.mk₀ a`. |
| A single j before diagrams are chosen | `∃ j : nerve A ⟶ K`, followed by vertex equality and then all E, H, c: exact quantifier order. |
| Every coherent target and diagram | `∀ (E : SSet.{u}) [Quasicategory E] (H : K ⟶ E)`: exact within the fixed simplicial universe of the recorded enhanced-diagram interface. No ordinary-category or strict-diagram substitution. |
| Every supplied coherent cocone | `c : (coconeCategory H) _⦋0⦌`: includes the actual apex and the complete transformation with its compatibility data. |
| Colimiting iff its restriction is colimiting | `IsColimiting H c ↔ IsColimiting (j ≫ H) ((gluingCoconeRestrict j H).app (op ⦋0⦌) c)`: both directions for the specified cocone, exactly as requested. |
| Same apex, restricted legs, natural in H | The existing `gluingCoconeRestrict` is actual precomposition on the whole transformation; its defining app keeps `z.1.1` literally. Internal-hom precomposition restricts arbitrary simplicial families, so the comparison is the natural restriction itself, without a diagram-dependent replacement choice. |
| No existence of all colimits | No cocompleteness or colimit-existence binder occurs. The predicates concern only c and its restriction. Exact. |

For dependency verification I opened `EnhancedDiagramsCones.lean`: `coconeCategory`
is the comma simplicial pullback for H → constant diagrams, and `IsColimiting`
means an initial object in that actual comma category, via contractible outgoing
mapping spaces. These are precisely the dependency node's conventions. I opened
`PushoutJoinSaturation.lean`: `orderedJoinFunctor` is the left Kan extension of
terminally augmented external products along ordinal concatenation, retaining both
pure summands, so the empty-base cone is still a point. I opened
`JoinSliceRightFibration.lean`: `orderedJoinInr` uses the empty left augmented block
and the right-block generator, hence selects the added right vertex. I opened
`InfinityColimitGluing.lean`: `gluingCoconeRestrict` preserves the apex and applies
`(ihom Δ[1]).map` to internal-hom precomposition, enforcing both endpoint equations
in every degree. These are already landed dependency interfaces, not new modules
or privately duplicated notions. Their owner-node additions to `stmt_deps` are
permitted by brief-stage2 §5. The three already stated proof dependencies are
imported non-publicly. The two decomposition nodes still have no Lean record;
their complete role is documented in the theorem's proof plan and does not affect
typing this statement.

Edge cases checked: A empty is excluded by the node itself (and by hA at ∅).
A singleton is allowed. Each B_a contains its displayed apex, so K empty cannot
satisfy these premises; this is a consequence, not an additional assumption.
Empty L_a is allowed. Empty E imposes no artificial nonemptiness assumption;
there is simply no H from the inhabited K in that case. Constant/point diagrams,
repeated cone vertices, overlapping or repeated subsets, and degenerate chains
are included. Degree zero is handled by the literal vertex formula. There are no
ring, characteristic, scheme, or additive-zero assumptions to restrict. The single
explicit universe u is arbitrary, with A, K, L and E in the recorded fixed universe;
there is no extra equality between site/object/morphism universes. No binder or
universe is left implicit under `set_option autoImplicit false`.

Independent existence searches used different wording from the worker:

- `msearch.py ... leanfinder`: “A filtered union of simplicial cones has a final
  functor selecting the apex of each cone”. Eight results were ordinary filtered
  category/cocone/final-functor statements. In particular I checked Mathlib's
  `CategoryTheory.IsFiltered.exists_directed`: it begins with an ordinary category
  and constructs a new directed poset, rather than using the given cone cover,
  prescribed vertices, and quasicategorical cocone test. It is not a match.
- `msearch.py ... leansearch`: “Finality of the simplicial nerve map selecting
  specified apices in an increasing filtered cover by right joins”. Eight results
  concerned nerves, nerve maps, simplicial thickening and nerve degeneracies;
  none states this theorem.
- `msearch.py ... loogle`: the initial two-string terminal query was malformed;
  the valid single-name query `"terminal"` returned unrelated parser/compiler
  declarations. This is recorded as inconclusive, not absence evidence.
- `rg` over upstream `WeilConjectures`, Mathlib's `AlgebraicTopology`, shared
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, using
  `cofinal.*[Cc]one|[Cc]one.*cofinal|final.*[Vv]ertex|[Dd]irected.*[Uu]nion|filtered.*[Uu]nion`,
  found final vertices of simplices, ordinary/pointwise cone material and unrelated
  unions. It found no competing directed-cone-cover statement. The exact theorem
  name was also searched in Mathlib, upstream, and shared Lean with no collision.
  Existing join, pure-right inclusion and cocone restriction constructions are
  reused; no new definition node or dependency repair is needed.

Mismatch found and repaired: the sandbox node had dropped the shared node's
`lean_audit` field. I restored that record verbatim, so the delivery changes only
`lean` and the three permitted landed-owner additions to `stmt_deps`. The Lean
statement and its docstring already match the node and source, and are unchanged.
There is no `statement_change`, so no correction/citer audit is required. Every
proof is `sorry` (the single item theorem), with all eight node proof steps in its
docstring and the source/blueprint marker present. There is no definition with
postponed data, no new axiom, no proof, no local notation, and no overwidth line.
The node's `lean.statement` was mechanically compared with the exact signature
from `theorem` up to `:= by` and is verbatim equal.

Validation: the required `scompile.py NP lem-coef-infinity-directed-cone-cover
lean/Sheaf/CategoryTheory/InfinityDirectedConeCover.lean` passed both sandbox and
library-path checks cleanly (1.5 s and 1.8 s); there are no sibling modules.
