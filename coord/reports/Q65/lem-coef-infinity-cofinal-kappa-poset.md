## Worker report

The module `Sheaf.CategoryTheory.InfinityCofinalKappaPoset` states
`SSet.Enhanced.exists_cofinal_kappa_directed_poset`, with its entire proof `sorry`.
There are no new definitions or other postponed declarations. The mathematical node
statement and proof are unchanged. The landed owner
`lem-coef-infinity-colimit-gluing` is added to `stmt_deps` to cite the actual cocone
restriction construction used in the statement (brief-stage2 §5).

Hypotheses and clauses, with the node and declaration open:

| Node text | Lean rendering |
| --- | --- |
| Universes U in U', small means U-small | `universe u v`; the index and poset are in `u`, while targets are in `max (u + 1) v`. `SSet.uliftFunctor.{max (u + 1) v, u}` performs the canonical degreewise lift for both index and indexing map. No equality between the small and containing universes is imposed. |
| Infinite regular cardinal κ in U | `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`. Mathlib's `Cardinal.IsRegular` has the field `aleph0_le`, so infinitude is included. |
| I is a U-small κ-filtered quasicategory | `(I : SSet.{u}) [Quasicategory I] (hI : SSet.Presentability.IsKappaFiltered κ I)`. A simplicial set with degreewise U-small sets is a U-small model. The dependency definition tests every κ-small simplicial diagram, including the empty one, using its nondegenerate-simplex cardinality predicate. |
| There exists a U-small partially ordered set A | `∃ (A : Type u) (_ : PartialOrder A) ...`. The partial-order instance supplies its ordinary category structure. |
| Coherent functor u : N(A) → I | `(f : nerve A ⟶ I)`. This is an actual simplicial map from the nerve, without replacing I by an ordinary category. |
| Every subset of size less than κ has an upper bound | `∀ s : Set A, HasCardinalLT s κ → ∃ b : A, ∀ a ∈ s, a ≤ b`. This quantifies over all subsets, rather than just finite ones. |
| Includes the empty subset, hence A is nonempty | There is no nonemptiness restriction on `s`. Taking `s = ∅` in the preceding clause produces an element `b : A`. A redundant separate nonemptiness conjunct is unnecessary. |
| Every coherent diagram in a quasicategory C admitting small colimits | `∀ (C : SSet.{max (u + 1) v}) [Quasicategory C], SSet.Presentability.HasSmallColimits.{u, max (u + 1) v} C → ∀ (F : SSet.uliftFunctor...obj I ⟶ C) ...`. The small-colimit hypothesis uses the original small universe `u`. |
| Restriction of a supplied colimiting cocone is colimiting | For every `c : (coconeCategory F) _⦋0⦌`, `IsColimiting F c → IsColimiting (SSet.uliftFunctor...map f ≫ F) ((gluingCoconeRestrict (SSet.uliftFunctor...map f) F).app (op ⦋0⦌) c)`. This is the first, defining formulation of cofinality explicitly given by the node. |
| Equivalent colimit comparison, natural in F and respecting restricted legs | The conclusion uses the existing actual restriction map, not an arbitrary cocone or merely existence of a colimit on the restricted shape. Its implementation keeps `c.1.1` as apex and precomposes the full coherent transformation via `MonoidalClosed.pre`. Thus its legs are exactly the original legs restricted by `f`, including higher simplices. Given any chosen colimits, their canonical comparison is the unique universal-property comparison with those legs. Saying this very cocone is colimiting makes that comparison an equivalence. Naturality in F is intrinsic to actual precomposition of entire coherent simplicial families. The node introduces this as an equivalent formulation, so no independent selection of colimits or maps is added to the theorem. |

Dependencies read and used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsKappaSmall`, `IsKappaFiltered`, `IsSmall`, and
  `HasSmallColimits`. Their signatures and docstrings were read in full. The first
  read of the DAG had no record for this dependency, but it landed during this task;
  the refreshed node and published source give the same module. Its existing
  declarations are used directly, and no dependency module is needed.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.coconeCategory` and `IsColimiting`, with the actual comma pullback
  and initial-object convention, together with Mathlib's `SSet`, `Quasicategory`,
  `nerve`, and `SSet.uliftFunctor`.
- `Sheaf.CategoryTheory.InfinityColimitGluing`:
  `SSet.Enhanced.gluingCoconeRestrict`. Read its complete implementation, including
  both coherent endpoint equations. It preserves the apex and restricts the whole
  transformation degree by degree.
- The stated proof dependencies are ordinary, non-public imports:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
  `Sheaf.CategoryTheory.InfinityJoinConeCalculus`, and
  `Sheaf.CategoryTheory.InfinityDirectedConeCover`. Their theorem signatures and
  proof docstrings were read. The module's theorem docstring records all four
  steps of this item's DAG proof and names these dependencies.
- `Mathlib.SetTheory.Cardinal.Regular`: `Cardinal.IsRegular`, whose definition
  explicitly includes infinitude. `HasCardinalLT` is the existing cardinal-bound
  predicate, applied to the subtype of members of each subset.

Source check: opened [Higher Topos Theory](https://www.math.ias.edu/~lurie/papers/highertopoi.pdf),
the March 2012 printing, Proposition the project server on printed pp. 383–384 (PDF pages
400–401), and Proposition the project server on printed p. 226. These are the poset-replacement
theorem and its colimit-invariance interpretation. No source-based correction is
needed. This online read does not claim an archive in `literature/`.

Edge cases checked before writing:

- Empty subset of A: its bound supplies nonemptiness; the clause cannot hold for
  an empty A. Empty I does not satisfy the supplied κ-filteredness predicate,
  because the diagram from the empty simplicial set would require a cocone apex.
- κ = aleph zero: the definition counts nondegenerate simplices, so κ-small
  simplicial sets are precisely those with finitely many nondegenerate simplices.
  The upper-bound condition tests finite subsets, including empty ones.
- Singleton I admits the singleton poset replacement; no spurious lack-of-final-
  object hypothesis from intermediate ordinary-category arguments is imposed.
- Empty target C is not excluded independently. Its small-colimit hypothesis
  fails already for the empty diagram, as it should.
- C may live in any containing universe `max (u + 1) v`. The source I and the
  replacement A remain in the original small universe, and F is a diagram from
  its canonical lift. No universe truncation discards larger targets.
- The conclusion is about the restriction of each supplied cocone, so constant
  diagrams and diagrams with nontrivial higher coherent data retain their legs;
  it is not merely an equality of numbers of colimit objects.

Searches made (all through the prescribed wrapper or read-only source search):

- `msearch.py ... leanfinder "Every small kappa filtered quasicategory admits a
  cofinal functor from a small kappa directed poset"`: eight hits, chiefly
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`, its auxiliaries,
  and ordinary filtered-category results. No quasicategory replacement theorem.
- `msearch.py ... leansearch "A filtered infinity category has a cofinal directed
  poset"`: eight ordinary-category hits, including
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed` and
  `CategoryTheory.IsFiltered.exists_directed`.
- `msearch.py ... loogle '"IsCardinalFiltered", "Final"'`: three hits, ordinary
  final-functor/cardinal-filtered results. Read the full signature of
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed` at
  `Mathlib/CategoryTheory/Presentable/Directed.lean:528`: it requires an ordinary
  `SmallCategory J` and does not cover arbitrary quasicategories.
- `msearch.py ... grep 'cofinal|exists_cardinal_directed'
  CategoryTheory/Presentable`: eleven hits, all ordinary-category material.
- `rg` of the upstream `WeilConjectures` tree for the item id, cofinality,
  κ-smallness and κ-filteredness found no matching theorem. `rg` for the proposed
  declaration name in upstream, Mathlib and `dag/lean_names_upstream.json` found
  no collision.
- `rg` of `lean/Sheaf/CategoryTheory` for `IsKappaSmall`, `IsKappaFiltered`,
  `PresentableInfinity`, `Cofinal`, `IsCofinal`, cocone restriction and small
  colimits located the landed definitions and `InfinityDirectedConeCover`,
  whose theorem requires a supplied cone cover and does not state this item.
  Further search for cofinal κ-filtered-poset replacement found no duplicate.
- `scompile.py --source Sheaf.CategoryTheory.PresentableInfinityCategory`
  confirmed the current published dependency source as it landed.

Validation: the single delivered module compiled through `scompile.py Q65
lem-coef-infinity-cofinal-kappa-poset .../InfinityCofinalKappaPoset.lean` in both
sandbox and library-module modes (1.5 s and 1.6 s). No errors or warnings were
printed. All variables and universes are explicitly bound; `autoImplicit` is
disabled. The file has only the intended theorem with a `sorry` proof and every
line is within 100 characters. There is no `STATEMENT-DISPUTED` flag, new node,
dependency repair, or statement correction.

## Second reading by Q65

I did not write this statement. I read the sandbox node and module against the
March 2012 HTT text, Proposition the project server, printed pp. 383–384, and Proposition
the project server(3), printed p. 226, opening the surrounding definition the project server and example
the project server as well. This source is HTT, not a Stacks result: there is no Stacks .tex
source place for this node. Proposition the project server assumes a κ-filtered infinity
category and constructs a κ-filtered poset with a cofinal nerve map. Definition
the project server assumes regular κ; example the project server translates filteredness of the nerve
into upper bounds for all κ-small subsets. No further finiteness, final-object,
or ordinary-category hypothesis is assumed. The node deliberately uses the
colimit-preservation consequence in small-cocomplete targets.

My object/hypothesis/conclusion checklist, matched with the Lean:

| Node item | Exact Lean rendering and verdict |
| --- | --- |
| Small universe and containing universe | `universe u v`, with small models in `u` and targets in `max (u + 1) v`. The canonical `SSet.uliftFunctor` lifts diagrams and indexing maps degreewise. Matches the two-universe convention without equating them. |
| Infinite regular small cardinal κ | `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`. I opened Mathlib's `IsRegular`: its `aleph0_le` field supplies infinitude. Exact. |
| Small κ-filtered quasicategory I | `(I : SSet.{u}) [Quasicategory I] (hI : SSet.Presentability.IsKappaFiltered κ I)`. The recorded dependency tests every κ-small simplicial diagram, including the empty diagram; no ordinary-category restriction. Exact. |
| One small partially ordered A and coherent map, chosen before testing diagrams | `∃ (A : Type u) (_ : PartialOrder A) (f : nerve A ⟶ I)`, outside all target, diagram, and cocone quantifiers. The poset's standard category structure gives the required nerve. Exact order of quantifiers. |
| Every subset of cardinality less than κ has an upper bound | `∀ s : Set A, HasCardinalLT s κ → ∃ b : A, ∀ a ∈ s, a ≤ b`. The cardinal predicate measures the subtype of members of s. No finite-only or nonempty-subset restriction. Exact. |
| Empty subset and nonemptiness | The same clause permits `s = ∅` and requires `b : A`. Nonemptiness follows rather than being omitted or assumed. Exact. |
| All coherent diagrams in every small-cocomplete target quasicategory | `∀ (C : SSet.{max (u + 1) v}) [Quasicategory C], HasSmallColimits.{u, max (u + 1) v} C → ∀ (F : SSet.uliftFunctor…obj I ⟶ C)`. The existing predicate tests all small simplicial shapes in the original small universe. Exact. |
| Restriction of every supplied colimiting cocone is colimiting | `∀ (c : (coconeCategory F) _⦋0⦌), IsColimiting F c → IsColimiting (SSet.uliftFunctor…map f ≫ F) ((gluingCoconeRestrict (SSet.uliftFunctor…map f) F).app (op ⦋0⦌) c)`. This uses the actual restriction of this very cocone, not existence of an unrelated colimit. Exact. |
| Equivalent canonical colimit comparison, natural in F, preserving restricted legs | The node expressly gives this as an equivalent formulation. The primary formulation above suffices: the universal property makes the canonical comparison from the restricted colimit to the original apex an equivalence. Actual precomposition specifies its legs and commutes with coherent transformations, yielding naturality. No independent comparison choice is required. Exact. |

I opened the dependency declarations themselves. In
`Sheaf.CategoryTheory.PresentableInfinityCategory`, `IsKappaSmall` counts the
sigma type of nondegenerate simplices over all dimensions, `IsKappaFiltered`
requires actual coherent cocones, and `HasSmallColimits` uses `IsSmall.{u}` and
`IsColimiting`. In `EnhancedDiagramsCones`, `coconeCategory` is the specified
coherent comma construction, and `IsColimiting` is its initial-object predicate,
using contractibility of outgoing mapping spaces. These are precisely the
objects of the dependency nodes, not similarly named ordinary notions.

I read the full construction of `gluingCoconeRestrict` in
`InfinityColimitGluing`, including both endpoint equations and naturality.
Its output in every degree has first coordinate `z.1.1` and second coordinate
the coherent transformation precomposed by the indexing map through
`MonoidalClosed.pre`. Thus it retains the original apex, all legs and their
higher compatibilities. Its owning node records it in `lean.declarations`;
adding that already landed owner to `stmt_deps` is authorized by §5. It does not
impose the pushout hypotheses of the separate gluing theorem. I also opened
the signatures and proof plans of the three proof-only imports: enhanced
functor/cone calculus, join/cone calculus, and directed cone cover. The delivered
docstring faithfully records all four proof steps, including the coordinate
homotopy, fresh-coordinate injectivity, regular-cardinal union bound, and final
composition of restrictions.

Edge cases: empty I fails filteredness because the empty diagram needs a cocone
apex; empty A fails the empty-subset upper-bound clause. Singleton I is permitted.
At κ = ℵ₀ the hypotheses test shapes with finitely many nondegenerate simplices,
and the conclusion tests all finite subsets. Finite κ is excluded exactly by
regularity's infinitude field. Empty target C cannot satisfy small cocompleteness.
Constant diagrams and higher coherent diagrams are both tested without alteration.
There is no scheme, ring, characteristic or degree parameter to restrict. Targets
may inhabit any containing universe of the displayed form; the indexing objects
remain small. All variables and universe levels are explicitly bound.

Independent duplicate searches, using new phrasings:

- `msearch.py … leanfinder "quasicategory regular cardinal filtered cofinal nerve partially ordered set"`
  returned eight hits, including `CategoryTheory.Nerve.quasicategory` and ordinary
  cardinal-filtered cocone results; no replacement theorem for quasicategories.
- `msearch.py … leansearch "Every filtered quasicategory is the cofinal image of the nerve of a directed partial order"`
  returned ordinary filtered-category results and
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`.
- `msearch.py … loogle '"Final", "PartialOrder"'` returned zero hits.
- Independent `rg` searches for `cofinal`, `Cofinal`, `IsKappaFiltered`,
  `kappa.*(cofinal|poset)` and the proposed declaration name in the named upstream,
  Mathlib presentability, project category-theory and upstream-name-index paths
  found no exact duplicate. I opened Mathlib's
  `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed` at
  `CategoryTheory/Presentable/Directed.lean:528`: it requires `SmallCategory J`
  and returns an ordinary final functor, so cannot replace this theorem.
  The project directed-cone-cover theorem requires additional supplied cone
  presentations and a cover; it does not state this item.

No mathematical or implementation mismatch was found; I left the Lean and node
unchanged and appended this independent reading only. There are no new definition
nodes, dependency repair modules or statement corrections to audit. The only
node fields differing from the shared base are `lean` and the authorized
`stmt_deps` addition. The module contains exactly one named theorem, with the
entire proof `sorry`, no new definitions, and no overlong lines. Its
`lean.statement` is verbatim equal to the source signature. Fresh validation by
`scompile.py Q65 lem-coef-infinity-cofinal-kappa-poset` compiled the sole file in
sandbox and library-module modes (1.5 s and 1.6 s), with no errors or warnings.
