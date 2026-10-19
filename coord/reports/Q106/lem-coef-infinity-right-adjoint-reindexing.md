## Worker report

Item: `lem-coef-infinity-right-adjoint-reindexing`, group Q106, stage 2.
Module: `Sheaf.CategoryTheory.InfinityRightAdjointReindexing`.
Declaration: `SSet.Enhanced.infinity_right_adjoint_reindexing`.
The single theorem has proof `sorry`; this delivery defines no new data and proves no theorem.

The original mathematical statement is unchanged. I added two already landed nodes to
`stmt_deps`, as authorized by coord/brief-stage2.md §5 (STMT_DEPS MAY GAIN LANDED NODES):
`lem-coef-infinity-mapping-excision` owns `excisionMappingRestriction`, and
`lem-coef-infinity-colimit-gluing` owns `gluingCoconeRestrict`. Only their canonical
construction helpers are used, not their excision or gluing theorems. Both helpers
already construct precisely the required restrictions. No new nodes or dependency
repairs are necessary. No maintenance repair note exists for this item.

Hypothesis and clause correspondence:

- Small ordinary categories in a fixed universe: `{I J : Type u}` with
  `[SmallCategory I] [SmallCategory J]`. The target is independently enlarged to
  `SSet.{max u v}`. The nerves and their map are transported there by the existing
  `SSet.uliftFunctor.{v}`. This is degreewise universe lifting, with unchanged
  simplex operators, and imposes no equality between indexing and target sizes.
  Below, `N(J)` and `N(R)` denote these canonically lifted nerves and map.
- Functors `L : J → I` and `R : I → J`: `(L : J ⥤ I) (R : I ⥤ J)`.
- Natural Hom bijections `Hom_I(Lj,i) ≃ Hom_J(j,Ri)`: `(adj : L ⊣ R)`.
  Mathlib `Adjunction.homEquiv adj j i` has exactly this signature and is natural
  in both arguments. The adjunction structure additionally records the uniquely
  determined unit and counit, not any extra mathematical hypothesis.
- Any quasicategory in the enlarged ambient universe:
  `(E : SSet.{max u v}) [Quasicategory E]`.
- Every coherent diagram `p : N(J) → E`: `∀ (p : SSet.uliftFunctor.{v}.obj (nerve J) ⟶ E)` in the first and
  last conjuncts. Mathlib `nerve` is the recorded ordinary nerve convention.
- Every vertex `e`: `(e : E _⦋0⦌)`. The constant diagram is `SSet.const e`;
  its vertex in the internal functor simplicial set is `diagramVertex (SSet.const e)`.
- The actual restriction map is an equivalence of spaces: the first conjunct is
  `IsWeakHomotopyEquivalence (excisionMappingRestriction (SSet.uliftFunctor.{v}.map (nerveMap R)) p
  (SSet.const e))`. The helper's full type is
  `mappingSpace ((ihom T).obj C) (diagramVertex F) (diagramVertex G) ⟶
  mappingSpace ((ihom S).obj C) (diagramVertex (a ≫ F)) (diagramVertex (a ≫ G))`.
  Its construction is exactly `mappingSpaceMap ((MonoidalClosed.pre a).app C)
  (diagramVertex F) (diagramVertex G)`. Here `a = SSet.uliftFunctor.{v}.map (nerveMap R)`, `F = p`, and
  `G = SSet.const e`; `a ≫ G` is the constant diagram on `N(I)` definitionally.
  Thus no arbitrary equivalent replacement of the map is used. The dependency
  defines equivalence of spaces by realization weak homotopy equivalence;
  the functor-calculus and pinch lemmas give Kan mapping spaces for these objects.
- Naturality in `p` and `e`: the second conjunct says the entire constant-diagram
  simplicial map commutes with restriction. The third conjunct quantifies over
  every parameter simplicial set `T` and every family
  `H : T ⟶ (ihom (SSet.uliftFunctor.{v}.obj (nerve J))).obj E`, and specifies
  `uncurry (H ≫ pre(N(R))) = (N(R) ▷ T) ≫ uncurry H`.
  This is a formula for the canonical restriction on whole families, not a claim
  about only components or isolated vertices. For `T = Δ[n]`, it retains all
  higher transformations; for parameter products with `Δ[1]` or `Δ[2]`, it gives
  restriction of transformation/square/triangle families and compatibility with
  precomposition and postcomposition. Maps between parameter sets commute by
  ordinary composition of simplicial maps. Faces and degeneracies commute since
  `pre(N(R))` is a simplicial map. Together with the constant-diagram equality,
  this is coherent naturality in the varying source diagram and vertex. This is
  the same all-parameter convention used by the landed mapping-excision module.
- Any specified coherent cocone: `(a : (coconeCategory p) _⦋0⦌)`.
  Its first data coordinate `a.1.1` is its actual vertex, and its second is its
  coherent transformation with the recorded endpoint equations.
- Colimiting if and only if the restriction is colimiting: the last conjunct uses
  exactly `IsColimiting p a ↔ IsColimiting (N(R) ≫ p)
  ((gluingCoconeRestrict N(R) p).app _ a)` (using the lifted-nerve convention above).
  Both sides use the dependency's initial-object predicate in the coherent comma
  cocone category, not a new universal-property predicate.
- Same vertex: the final equality is
  `((gluingCoconeRestrict N(R) p).app _ a).1.1 = a.1.1`.
  The helper retains the vertex coordinate and postcomposes only the coherent arrow
  with the internal-hom precomposition map.
- No other colimits assumed: there is no existence, completeness, cocompleteness,
  nonemptiness, filteredness, fullness, or edge-invertibility hypothesis.

Declarations used, with source signatures and docstrings read:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `constantDiagrams`, `coconeCategory`,
  `IsColimiting`, `IsWeakHomotopyEquivalence`; these are the recorded definitions
  of the original statement dependency, not privately redefined versions.
- `Sheaf.CategoryTheory.InfinityMappingExcision`:
  `SSet.Enhanced.excisionMappingRestriction`, canonical right-pinched restriction.
- `Sheaf.CategoryTheory.InfinityColimitGluing`:
  `SSet.Enhanced.gluingCoconeRestrict`, canonical coherent comma restriction.
- `Mathlib.AlgebraicTopology.SimplicialSet.Nerve`: `CategoryTheory.nerve`,
  `CategoryTheory.nerveMap`; imported publicly through the enhanced definitions.
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`: `SSet.uliftFunctor`, the
  degreewise universe lift `SSet.{u} ⥤ SSet.{max u v}`; its construction and
  docstring were read before introducing the explicit target universe.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction` and
  `CategoryTheory.Adjunction.homEquiv`, with its two naturality laws.
- `MonoidalClosed.pre`, `MonoidalClosed.uncurry`, and `ihom` are Mathlib's
  existing cartesian closed constructions. `uncurry_pre_app` has the exact
  family formula displayed in the statement.

Every already stated proof dependency is imported without `public`:
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`
(`SSet.Enhanced.enhanced_functor_cone_calculus`),
`Sheaf.CategoryTheory.HomotopyEquivalenceWeak`
(`SSet.Enhanced.homotopy_equivalence_weak`),
`Sheaf.CategoryTheory.InfinityMappingComposition`
(`SSet.Enhanced.mapping_composition`),
`Sheaf.CategoryTheory.RightPinchComparison`
(`SSet.Enhanced.right_pinch_comparison`), and
`Sheaf.AlgebraicTopology.RealizationCylinder` (`SSet.realization_cylinder`).
The module docstring and theorem docstring give the source and all seven proof steps.

Edge cases checked mathematically before writing (and size refinement checked before handoff):

- Identity adjunction: both restriction maps are identities.
- `R : I → point` when `I` has an initial object (its left adjoint): cocones on
  the constant diagram are determined by that initial object. Empty `I` cannot
  admit the required left adjoint from the point, so no false empty-shape case enters.
- `R : point → J` selecting a terminal object: restriction computes the given
  colimit at that terminal object, in the correct right-adjoint direction.
- Empty `I` and `J`: the adjunction exists, restriction is the identity on the
  empty-shape functor category, and the cocone property is still tested exactly.
- Non-full right adjoint, such as the map from a nontrivial chain to the point:
  no fullness hypothesis or simplification to a full subcategory is present.
- Empty target quasicategory: vertex and cocone quantifiers become empty where
  appropriate; no artificial nonempty instance is required.
- Strictly larger target universes are handled by the explicit `max u v` and
  degreewise universe-lift functor, as in other landed coherent restriction modules.
- Empty mapping spaces, arbitrary higher parameter simplices, and constant
  transformations are retained by the existing mapping-space definitions.
- The variance of the parent application is `R = j.op`, `L = r.op`; this agrees
  with its existing proof step 4. Reversing the adjunction would give a false
  colimit statement. No statement dispute or statement correction was needed.

Searches (fresh logged msearch calls, in addition to source inspection):

- LeanFinder: "Restriction along the nerve of a right adjoint induces equivalences
  of coherent cocone mapping spaces in every quasicategory". Eight hits, principally
  `nerveAdjunction`, `Truncated.nerve₂Adj`, reflective nerve and homotopy-category
  constructions. None states coherent cocone restriction for an arbitrary target.
- Loogle: `CategoryTheory.Functor.final_of_adjunction,
  CategoryTheory.Functor.Final.isColimitWhiskerEquiv`. Zero hits for this combined
  query. I separately read `Limits/Final.lean:130–165` and its ordinary-category
  `final_of_adjunction`: it does not state this quasicategorical conclusion.
- Mathlib grep through msearch: `adjunction|cofinal|reindex` in
  `AlgebraicTopology/Quasicategory`. Zero hits.
- LeanSearch: "An ordinary right adjoint preserves and detects coherent colimit
  cocones in any quasicategory by restriction on mapping spaces". Eight hits;
  right-adjoint preservation of ordinary limits, `IsColimit.ofLeftAdjoint`, and
  ordinary adjoint-functor/Kan-extension results. None is an exact match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `right.adjoint.*(reindex|cofinal)|rightAdjointReindex|right_adjoint_reindex|
  lem-coef-infinity-right-adjoint-reindexing`: only the parent split-augmentation
  docstring mentions the item; no existing declaration states it.
- Semantic/name grep of `lean/Sheaf/CategoryTheory` found the two reusable
  canonical restriction helpers above. Their owning nodes have landed records;
  I read their constructions and reused them, adding the corresponding DAG edges.

Source check: opened the current blueprint ancestor proof paragraph 2 in
`literature/blueprint/main-20261015/.../prop-coef-integral-exceptional-adjoint.proof.md`
and the online [HTT PDF](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
checking cofinality §4.1, especially the project server–8 and the project server. An ordinary adjunction
makes `j/R` have initial object `(Lj, unit_j)`, consistent with the direction of
this item and with its seven-step direct unit/counit proof.

Validation: `scompile.py Q106 lem-coef-infinity-right-adjoint-reindexing
lean/Sheaf/CategoryTheory/InfinityRightAdjointReindexing.lean` compiled the sandbox
and the real module path cleanly (about 1.4 s and 1.7 s) for the final version
with explicit universe lift. The first compile also compiled the side-overlay
realization-cylinder proof dependency. The preliminary dry delivery passed before
this universe refinement; the required dry run is repeated on the final files. No errors or unexpected warnings.
All variables and universes are explicitly bound; no file-local notation, instance,
private definition, arbitrary comparison map, or new postponed helper is introduced.
The node's `lean.statement` is extracted verbatim from the theorem signature.

## Second reading by Q106

The node introduces small ordinary categories `I` and `J` in one universe, functors
`L : J ⥤ I` and `R : I ⥤ J`, and an adjunction `adj : L ⊣ R`; the Lean binders are
`{I J : Type u}`, the two `SmallCategory` instances, and `(L) (R) (adj)`.  The
adjunction binder is retained as an assumption even though its data is consumed by
the postponed proof rather than appearing syntactically in the conclusion.  It then
introduces an arbitrary quasicategory `E` in a sufficiently large universe; Lean uses
`E : SSet.{max u v}` with `[Quasicategory E]`, and degreewise `uliftFunctor.{v}` for
both nerves, so no equality of target and indexing universes is imposed.

The first conclusion clause quantifies every coherent diagram `p` on `N(J)` and
every vertex `e` of `E`, and asserts that the canonical restriction map from the
right-pinched mapping space to the restricted one is a weak homotopy equivalence.
Lean renders this with `excisionMappingRestriction (uliftFunctor.map (nerveMap R))
p (SSet.const e)`, exactly the dependency's canonical map.  The second clause is
the constant-diagram restriction equality.  The third is the all-parameter formula
for naturality: every `T` and `H : T ⟶ ihom (N(J)) E` satisfies the displayed
`uncurry`/precomposition equation, retaining higher transformation simplices.  The
last clause quantifies every coherent cocone `a` on every `p`, gives the exact
colimiting iff after restriction by `gluingCoconeRestrict`, and explicitly preserves
the apex vertex via `.1.1 = a.1.1`.  These are all clauses of the node, in the same
order and with no extra existence or colimit hypotheses.

Edge cases were checked: identity adjunctions, right adjoints selecting an initial or
terminal object, non-full right adjoints, empty indexing categories, empty target,
zero/empty mapping spaces, arbitrary parameter simplices, and `n = 0` vertices.  The
adjunction direction is `L ⊣ R`; reversing it would give the wrong colimit assertion.

I searched Mathlib and the upstream/source trees with LeanSearch, LeanFinder, Loogle,
and `rg` for right-adjoint reindexing, cofinality, and the declaration name.  Only
ordinary-category finality results were found; no existing declaration states this
quasicategorical result.  The two added statement dependencies are already landed
nodes, and their declarations were read: `excisionMappingRestriction` and
`gluingCoconeRestrict` are the canonical constructions used here.  No new node,
dependency repair, duplicate definition, hollow definition, or statement correction
was needed.  The module compiled cleanly with `scompile.py`; no source or statement
changes were made.
