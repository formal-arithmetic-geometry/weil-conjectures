## Worker report

The new module `Sheaf.CategoryTheory.InfinityEquivalenceCocartesianTests` states
`SSet.Enhanced.infinity_equivalence_cocartesian_tests`. Its only theorem has proof
`sorry`; it defines no new notion, chooses no object, and changes only the item's
`lean` record. Q94's earlier landing was a stage-1 split, not a Lean attachment:
the base node has no `lean` record. The previous unchanged-node rejection therefore
does not apply to this new stage-2 module and record.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small quasicategories E, F, B are arbitrary `SSet.{u}` with the three explicit
  `Quasicategory` instances. The single universe is the fixed small universe of
  the node; there is no small-hom-space hypothesis and no upper universe bound.
- The maps p:E→B and q:F→B are the binders `p` and `q`.
  `_hp : InnerFibration p` and `_hq : InnerFibration q` are exactly the two
  inner-fibration hypotheses. No lifts of any other edge are assumed.
- The enhanced functor T is `T : E ⟶ F` and its functor-equivalence hypothesis is
  `_hT : IsFunctorEquivalence T`. This is the recorded definition with a
  quasi-inverse and coherent natural equivalences, including inverse triangles.
- Strict commutation qT=p is `_hbase : T ≫ q = p`.
- The fixed edge is `e : Δ[1] ⟶ E`. `x`, `y`, `_hex`, `_hey` merely name its
  uniquely determined source and target; the face convention is δ1=source,
  δ0=target. These equations restrict no edge. Its image is `e ≫ T`.
- The hypothesis at EVERY image test vertex is `himage : ∀ z : E _⦋0⦌, ...`.
  The existential formula following it is exactly the right-hand criterion in
  `infinity_cocartesian_mapping_criterion` instantiated with q, T(x), T(y),
  T(e), and test vertex T(z). In particular, the equation involving
  `arrowMappingSpaceInclusion` fixes `a` to T(e); `a` is not an arbitrary edge.
- The top arrow is `cocartesianPrecomposition F ... a`. The left vertical arrow
  `g` is fixed by its equation after `cocartesianPrecompositionInclusion` to
  applying q to the WHOLE triangle. The right vertical arrow is `arrowSpaceMap q`.
  The bottom arrow is the corresponding `cocartesianPrecomposition B`. These
  are the existing canonical triangle roofs presenting the exact mapping square,
  rather than independently chosen representatives of composition classes.
- Homotopy pullback is the dependency's `IsHomotopyPullbackSquare`, which includes
  the strict commutation equation and weak equivalence of the canonical map to
  the path-space pullback. The roof and natural right-pinch comparisons are
  precisely those already used in the recorded mapping criterion. Thus changing
  to the roof presentation does not change the homotopy-pullback test.
- The conclusion `∀ w : F _⦋0⦌, ...` is the identical canonical criterion at
  arbitrary w. It asserts neither a reflection statement for e nor additional
  cocartesian lifts. In particular it never confuses a vertex of E with one of F.
- The node's final sentence specifies the transport argument. The docstring
  follows all four proof steps: evaluate the coherent TS→id equivalence and both
  inverse triangles; apply q to those same simplices; restrict the coherent
  Hom comparison to T(e) and curry to Φ; apply Φ to the equivalence with its
  inverse triangles; use whole-square invariance and path-pullback recognition.
  No arbitrary commutation homotopy, or equality only of corner/edge classes,
  replaces that coherent comparison.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `IsFunctorEquivalence`, `AreNaturallyEquivalent`, `IsEquivalenceEdge`,
  `diagramVertex`, `evaluation`, and the recorded right-pinched `mappingSpace`.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` is the current
  module recorded for `def-coef-infinity-fibrations`. It publicly imports the
  original `InfinityFibrations` with the horn definitions. We import the current
  recorded module; `InnerFibration` is Mathlib's own notion.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `mapping_composition` and
  `MappingCompositionStatement`, read in full. It is publicly available through
  the mapping-criterion module; its canonical composition classes identify the
  triangle roofs with the stipulated precomposition maps.
- `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`:
  `infinity_hom_bifunctor_functoriality`, `HomBifunctorData`, and
  `HomBifunctorComparison`, read with their full signatures and docstrings.
  This proof dependency is imported non-publicly. Its containing-universe
  interface is not imposed as an extra size hypothesis on this statement.
- `Sheaf.CategoryTheory.KanNervePullbackRecognition`:
  `kan_nerve_pullback_recognition` and `KanSquarePresentation`, read in full;
  imported non-publicly for the specified-commutation and whole-square clauses.
- `Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion`:
  `infinity_cocartesian_mapping_criterion`, `cocartesianPrecompositionSource`,
  `cocartesianPrecompositionInclusion`, `cocartesianPrecomposition`; their actual
  definitions and complete theorem were read. Both criterion formulas are direct
  instantiations of that theorem's right-hand side. `arrowSpaceMap` and
  `arrowMappingSpaceInclusion` are its existing arrow-space interface.

Source checked: the online HTT PDF, printed pp. 131–132, Proposition the project server
and its proof (https://www.math.ias.edu/~lurie/papers/HTT.pdf). The displayed
criterion uses an arbitrary test object; this item transports the dual criterion
along essential surjectivity using the coherent Hom and recognition inputs.

Edge cases checked: T the identity and w=Tz; degenerate e; B=Δ[0]; empty
mapping spaces; empty E/F. No nonemptiness hypothesis is introduced. With an
edge e the source cannot actually be empty; if F is empty the displayed universal
conclusion is vacuous. Equivalence excludes a genuinely missing connected
component of F. No criterion is silently restricted to identity base edges.

Searches made (raw remote results are retained in sandbox `searches.jsonl`):

- `msearch.py leanfinder`, query “Homotopy pullback mapping criterion squares at
  all essential image vertices transport to every test vertex along an equivalence
  of quasicategories”: eight hits, principally truncated homotopy-category and
  homotopy-conversion declarations; no matching test-object transport theorem.
- `msearch.py loogle`, query `"Quasicategory", "equivalence"`: zero hits.
- `msearch.py grep`, query
  `equival.{0,80}(cocartesian|cartesian)|(cocartesian|cartesian).{0,80}equival`
  in Mathlib `AlgebraicTopology`: zero hits.
- `msearch.py leansearch`, query “Homotopy pullback mapping squares are invariant
  under equivalences of test objects in a quasicategory”: eight ordinary-category
  pullback-square equivalence/isomorphism results, no quasicategorical statement.
- Source `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for
  `equivalence_preserves_cocartesian`, essential-image transport, and
  equivalence/cocartesian combinations found adjacent ordinary-category,
  straightening and unrelated essential-image results, no exact declaration.
  Upstream `grep -rn` for the item's blueprint id gave no hit. A narrower search
  for named cocartesian criterion predicates found no reusable predicate; the
  existing criterion theorem's RHS is used directly, with no duplicate definition.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag
is needed. Validation: `scompile.py` compiled the module cleanly.
`deliver2.py --no-push` then compiled the final file and passed the server preflight
(OK, dry-run commit `22b2385897`). Only the item’s `lean` field changes; the
module has one theorem with `sorry`, explicit universes and `autoImplicit false`;
its maximum line width is 87 characters.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
