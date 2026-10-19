## Worker report

The module `Sheaf.CategoryTheory.UniversalLocalizationDegenerateEdges` states
`SSet.Enhanced.universally_localizing_degenerate_edges`. It has one theorem with a
`sorry` proof, and introduces no definition or auxiliary node. The node's two statement
dependencies are imported directly.

The hypotheses and conclusion render the node as follows:

- `A` and `B` are arbitrary small simplicial sets, both in `SSet.{u}`, and `f` is the
  simplicial map `f : A ⟶ B`. There are no quasicategory, Kan, finiteness, or
  nonemptiness assumptions on either one.
- `hf : IsUniversallyLocalizing f` is the universal-localization hypothesis, using the
  dependency's definition. It quantifies over every small base change and chooses a
  collection before the test quasicategory.
- The conclusion quantifies over every `E : SSet.{max u v}` and assumes exactly
  `Quasicategory E`; `v` is an explicit, freely enlarging target universe.
- The edge collection is exactly
  `{w | ∃ b : B _⦋0⦌, f.app _ w = B.σ 0 b}`. Thus `w` ranges over all degree-one
  simplices of `A`, and membership means that its image is a degenerate edge coming
  from a degree-zero simplex of `B`.
- The witness `r` has source
  `(ihom (SSet.uliftFunctor.{v, u}.obj B)).obj E`, the coherent functor simplicial set
  `Fun(B,E)` after the recorded universe transport, and target the `toSSet` of
  `edgeInvertingDiagrams A W E`, the full subcategory of `Fun(A,E)` on diagrams that
  carry every edge in `W` to an equivalence.
- The equation
  `r ≫ (edgeInvertingDiagrams A W E).ι =
  (MonoidalClosed.pre (SSet.uliftFunctor.{v, u}.map f)).app E`
  says that `r` is restriction along `f`, with the factorization holding in every
  simplicial degree through the full subcategory inclusion.
- `IsFunctorEquivalence r` is the dependency's coherent equivalence notion: it supplies
  a quasi-inverse and coherent natural equivalences of both composites, including the
  inverse-triangle witnesses. This is the asserted equivalence onto the full
  edge-inverting subcategory.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declaration
  `SSet.Enhanced.IsFunctorEquivalence` (and its `SSet.Enhanced` coherent diagram
  conventions).
- `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`, declarations
  `SSet.Enhanced.edgeInvertingDiagrams` and
  `SSet.Enhanced.IsUniversallyLocalizing`.

The proof docstring records the eight proof steps from the node: base-change
localization, ordered-simplex degenerate-edge analysis, equality of full diagram
subcategories by the inverse-square argument, finite boundary-cell gluing, pullback
pushout bookkeeping, filtered colimit over finite simplicial subsets, and specialization
to the identity base change.

Edge cases checked include `A = ∅`, `B = ∅`, the empty test simplicial set `E`, a
zero-simplex standard simplex (`n = 0`), identity maps, all-degenerate maps, and
universe enlargement with `v = 0` or `v > u`. The theorem imposes no hidden
nonemptiness or Kan condition; the `Quasicategory E` implication is the only condition
on the target.

Searches made before writing:

- `msearch.py Q24 lem-coef-universal-localization-degenerate-edges leanfinder` for
  universal localization at degenerate-image edges: no matching coherent theorem.
- `msearch.py ... loogle "SSet, Localization"` and
  `msearch.py ... loogle "simplicial universal localization edge inversion"`: no usable
  match; returned ordinary categorical localization names only.
- `msearch.py ... grep "universally.?[Ll]ocaliz|degenerate.*localiz|localiz.*degenerate"`
  and grep for `universally localizing simplicial`: no Mathlib or project declaration.
- `rg` over `WeilConjectures/` and `lean/Sheaf/`: only the two recorded dependency
  notions and unrelated ordinary localizations were found.

The item statement is mathematically coherent and no `STATEMENT-DISPUTED` flag is
needed. The module compiles cleanly with `scompile.py`; the only postponed proof is the
single theorem proof required by stage 2.

## Earlier second reading (a previous round; superseded)

I reread the node, its two dependency records, and the complete theorem signature.
`A`, `B`, `f`, `E`, and the universe parameters correspond exactly to the node. The
set-builder uses precisely degree-one edges whose image equals `B.σ 0 b`; no arbitrary
edge collection is substituted. The target is the full coherent functor subcategory
provided by `edgeInvertingDiagrams`, and the displayed equation pins `r` to restriction
along `f`. The final conjunct is exactly `IsFunctorEquivalence`, with no extra clauses or
hypotheses. No mismatch was found.


## Second reading by Q24

I independently opened the item node, its eight proof steps, both statement-dependency
nodes and their Lean source modules, the actual edge-inverting subcategory construction
in `EnrichedMarkedRealization.lean`, and the theorem in this sandbox. There are no new
nodes or dependency modules in this delivery, no `statement_change`, and no repair note
for this item. The earlier second-reading paragraph above is superseded by this reading.

The source is Kerodon, not Stacks. I read [Corollary the project server, 02M2](https://kerodon.net/tag/02M2),
[Proposition the project server, 02M1](https://kerodon.net/tag/02M1),
[Proposition the project server, 01MS](https://kerodon.net/tag/01MS), and
[Definition the project server, 02M0](https://kerodon.net/tag/02M0) online. The Stacks tag table
assigns these same strings to unrelated algebra/constructions statements; those are not
the source. Kerodon 02M2 has arbitrary simplicial source and target and exactly the
specified collection of edges. Kerodon 01MS(2) supplies the full coherent functor-category
form for arbitrary simplicial shapes, without requiring those shapes to be quasicategories.
The node and its source agree; no natural-language statement correction is needed.

Object, hypothesis and conclusion checklist (my reconstruction of the node):

1. Small simplicial sets `A` and `B`, with no additional structures or properties:
   `{A B : SSet.{u}}`. Verdict: exact; Mathlib's simplicial presheaves and their
   degreewise limits are the dependency's objects.
2. A simplicial map from `A` to `B`: `(f : A ⟶ B)`. Verdict: exact, including all
   naturality conditions supplied by a natural transformation.
3. Universal localization of that map, meaning every small base change is localization
   at some edge collection, chosen before the test quasicategory:
   `(hf : IsUniversallyLocalizing.{u, v} f)`. I opened the dependency definition:
   it quantifies over `(T : SSet.{u}) (g : T ⟶ B)`, then `∃ W`, then uses
   `IsLocalizationAtEdges.{u, v}`. Verdict: exact after the universe repair below.
4. Precisely the edges of `A` whose images are degenerate edges of `B`:
   `{w | ∃ b : B _⦋0⦌, f.app _ w = B.σ 0 b}` in each occurrence of
   `edgeInvertingDiagrams A ... E`. Here the expected `Set (A _⦋1⦌)` fixes the
   degree of `w`; the only degeneracy from vertices is `σ 0`. Verdict: exact,
   with the existential vertex inside edge membership, not chosen globally.
5. Every test quasicategory in an arbitrary containing universe:
   `∀ (E : SSet.{max u v}), Quasicategory E →`. Verdict: exact, with explicit
   independent enlargement parameter `v`, no Kan assumption and no nonemptiness.
6. The coherent functor category from `B` to `E`:
   `(ihom (SSet.uliftFunctor.{v, u}.obj B)).obj E`. Verdict: exact;
   Mathlib's `uliftFunctor` is degreewise universe transport, and `ihom` is the
   simplicial internal hom, retaining higher coherent simplices.
7. The full subcategory of diagrams from `A` to `E` that invert every specified edge:
   `(edgeInvertingDiagrams A W_f E).toSSet`. I read its body: it reuses
   `EnrichedMarkedRealization.invertingDiagrams` on `uliftFunctor.obj A`, with
   transported membership `{e | e.down ∈ W_f}`. That construction is
   `fullSubcomplex` on the predicate that evaluates each marked edge and applies
   `SSet.Enhanced.IsEquivalenceEdge E`. The latter has one inverse edge and both
   triangular inverse witnesses. Verdict: exact full subcategory; no private copy,
   ordinary-category replacement or additional quasicategory assumption on `A`.
8. Restriction along `f` induces the map to this subcategory, rather than an arbitrary
   equivalence with the same endpoints: the witness `∃ r` is followed by
   `r ≫ (edgeInvertingDiagrams A W_f E).ι =
   (MonoidalClosed.pre (SSet.uliftFunctor.{v, u}.map f)).app E`.
   Verdict: exact equation of simplicial maps in every degree, not merely at vertices.
9. That induced map is a coherent functor equivalence: `IsFunctorEquivalence r`.
   Its dependency definition says `∃ g`, with coherent natural equivalences of
   both composites with their identities; `AreNaturallyEquivalent` uses an
   equivalence edge of the internal hom with prescribed endpoints. Verdict: exact.
10. No quasicategory, Kan, finiteness or nonemptiness restriction on `A` or `B`:
    there are no such binders or instances. Verdict: exact. The binders introduce
    all objects before using them, and the only hypothesis on `E` follows its binder.

Mismatches found and repaired:

- H3/H9, an unintended universe in the universal-localization hypothesis. I compiled
  a scratch copy through `scompile.py` with `pp.universes` and `#print`. The original
  theorem elaborated with three parameters `{u, v, u_1}` and hypothesis
  `IsUniversallyLocalizing.{u, u_1} f`, even though its conclusion tested
  `SSet.{max u v}`. The unannotated occurrence did not infer `v` from the later
  conclusion. I changed it to `IsUniversallyLocalizing.{u, v} f`, so the hypothesis
  and conclusion use the same arbitrary containing universe. This is a Lean
  rendering repair, not a correction of the node's natural-language statement.
- The file omitted imports of already stated proof dependencies. I added ordinary
  imports of `Sheaf.CategoryTheory.InfinityMappingComposition` and
  `Sheaf.CategoryTheory.PointwiseEquivalences`, plus the Mathlib leaf
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` containing
  `SSet.relativeCellComplexOfMono`. The remaining two localization-gluing proof
  dependencies have no recorded module yet, so there is no module to import.
- H8, the original proof docstring compressed steps 4--6 and did not spell out the
  pullback-pushout, injective-leg and edge-union checks. I expanded it into all eight
  node steps, naming the proof dependencies. It now includes the empty base, the
  zero-dimensional boundary, the inverse-square argument, the two finite inductions,
  filtered finite subsets, and the final identity-base-change identification.

No other statement clause changed. The node's only changed field is `lean`, and
`lean.statement` is extracted verbatim from the repaired theorem signature.
There is one theorem, whose proof remains `by sorry`; no definition, auxiliary
axiom, proved lemma, file-local notation, private declaration or new node was added.
The module and theorem docstrings give the source and the required blueprint id.
All Lean lines are at most 100 characters.

Edge-case reading:

- `A = B = ∅` is allowed; the edge set is empty and functor categories out of the
  empty shape are terminal. A map to empty `B` already forces empty `A`.
- Empty `A` and arbitrary `B` are admitted without asserting that every such map
  satisfies `hf`. No inhabitant is implicitly demanded anywhere in the signature.
- Empty target `E` is included whenever it satisfies Mathlib's inner-horn condition;
  no dimension-zero filling or vertex assumption was added.
- For `f = id`, the specified edges are exactly the degenerate edges. Simplicial
  maps send these to degenerate, hence equivalence, edges. The restriction map
  is the expected identity after universe transport and the full-subcategory factor.
- If all images of edges are degenerate, the collection is all edges; the statement
  retains this case and still requires the genuine universal-localization hypothesis.
- The proof includes `n = 0`, with empty simplex boundary. No integer/characteristic,
  ring, scheme, additive zero object, or separate index set occurs in the signature.
  The proof's finite-subset index contains the empty subset.
- Universes `u` and `v` are declared, `v = 0` includes tests in the source universe,
  and arbitrary larger `v` is allowed. Degreewise `ULift` transports `A`, `B`, `f`,
  and the edge collection consistently; no equality of independent universes is imposed.

Independent duplicate searches, 2026-10-17 (in addition to the worker's searches):

- `msearch.py ... leanfinder` with “A simplicial map whose every base change is a
  localization inverts edges mapping to degenerate one-simplices” returned Quillen
  generating morphisms, truncated homotopy-category predicates, `SSet.Quasicategory`,
  `SSet.IsStrictSegal`, and `SSet.degenerate_app_apply`. None states this theorem.
- `msearch.py ... leansearch` with “A universally localizing map of simplicial sets
  is a localization at the edges mapping to degenerate edges” returned `SSet.Edge.map`,
  `SSet.degenerate`, `SSet.mem_degenerate_iff`, `SSet.degenerate_iff_of_isIso`,
  `SSet.degenerate_zero`, `SSet.image_degenerate_le`, and truncated edge maps;
  none gives the coherent localization equivalence.
- Loogle `SSet, Quasicategory` did not resolve the unqualified second identifier;
  I reran with `SSet, CategoryTheory.MorphismProperty`, which returned only the
  Quillen generating cofibration/fibration predicates and inner fibrations, not a match.
- `msearch.py ... grep` with `localization.*simplicial|simplicial.*localization|degenerate.*invert`
  gave no match. Direct `rg -i` over Mathlib, `WeilConjectures/`, and `lean/Sheaf`
  with `universal.{0,25}localiz|localiz.{0,40}degener|degener.{0,40}localiz|degenerate.image`
  found the recorded universal-localization definition and unrelated localization
  constructions and consumers, not an existing theorem with this conclusion.
- I also searched the exact declaration name and both used notion names in the
  upstream-name table and both source trees. The exact theorem is absent, and
  the two recorded notions are used through their owning modules.

The dependency `EnrichedMarkedRealization.IsEdgeLocalization` is not a replacement:
I opened its signature and body; it additionally requires its target simplicial set
itself to be a quasicategory. The recorded `IsLocalizationAtEdges` correctly permits
arbitrary simplicial shapes. Thus an `existing: true` record would not be faithful.

Validation: `scompile.py Q24 lem-coef-universal-localization-degenerate-edges`
compiled the delivered module and a separate scratch inspection file successfully on
the server. The delivered module had no errors or warnings. The inspected repaired
theorem has exactly universe parameters `{u, v}`, hypothesis
`IsUniversallyLocalizing.{u, v} f`, and tests `SSet.{max u v}`; the unintended
`u_1` is gone. The scratch inspection file is not part of the delivery.
