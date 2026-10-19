## Worker report

The module `lean/Sheaf/CategoryTheory/AccessibleIndColimitExtension.lean` defines
`SSet.Presentability.compactFilteredHull`, the replete full subcomplex of a quasicategory
whose vertices are equivalent to coherent colimits of small κ-filtered diagrams with all
vertices satisfying the supplied predicate.  It also defines the universe-explicit helper
`SSet.Presentability.posetNerve` and states
`SSet.Presentability.accessible_ind_colimit_extension` with proof `sorry`.

The theorem uses the recorded declarations
`Sheaf.CategoryTheory.PresentableInfinityCategory`:
`SSet.Presentability.IsEssentiallySmall`, `IsKappaSmall`, `IsKappaFiltered`,
`IsKappaCompact`, `IsKappaAccessible`, `HasSmallColimits`, and
`PreservesColimitsIn`; and
`Sheaf.CategoryTheory.EnhancedDiagramsCones`:
`SSet.Enhanced.fullSubcomplex`, `coconeCategory`, `IsColimiting`, and
`IsEquivalenceEdge`.  The two modules are public imports.

The Lean rendering of each hypothesis is as follows.  `κ` is an infinite regular small
cardinal via `(hκ : κ.IsRegular)`.  `E` is the ambient quasicategory in universe
`max (u + 1) v`, with `[hE : SSet.Quasicategory E]`.  `P` is the vertex predicate for
`E_0`.  Essential smallness is
`hPsmall : IsEssentiallySmall (Enhanced.fullSubcomplex E P).toSSet`.
Repleteness is the equivalence-invariance clause
`hPreplete : ∀ e, IsEquivalenceEdge E e →
(P (E.δ 1 e) ↔ P (E.δ 0 e))`.
Compactness is `hPcompact : ∀ x, P x → IsKappaCompact E κ x`.
Closure under κ-small colimits computed in `E` is `hPcolimit`: for every
`K` with `IsKappaSmall κ K`, coherent `F : K ⟶ E` whose vertices satisfy `P`, and
colimiting cocone `t`, its apex `t.1.1` satisfies `P`.

The conclusion has five clauses.  First, it supplies the quasicategory instance
`hE1` for `compactFilteredHull κ P` and asserts
`@IsKappaAccessible ... hE1 κ`.  Second, it asserts
`HasSmallColimits` for that subcategory.  Third,
`PreservesColimitsIn (compactFilteredHull κ P).ι (fun I _ _ ↦ IsSmall I)` says that
its inclusion sends every colimiting small coherent cocone to a colimiting ambient
cocone, hence gives closure under all ambient small colimits and preservation by the
inclusion.  Fourth, every `P`-vertex is represented by a vertex of the hull, expressed
as `∀ x, P x → ∃ y, y.1 = x`; this is the one-object filtered presentation clause.
Fifth, every hull vertex `x` has a presentation by an explicitly universe-small
partially ordered type `A`, its explicit nerve `posetNerve A hA`, a quasicategory
witness `hN`, `IsSmall`, `@IsKappaFiltered`, a lifted coherent diagram `F` with
`P`-valued vertices, a colimiting cocone `t`, and an equivalence edge whose endpoint
is `x.1`.  The endpoint equations use the same orientation as
`SSet.Presentability.IsKappaAccessible`.

The helper `posetNerve` only packages the ordinary category instance induced by the
explicit `PartialOrder`; it introduces no mathematical assumption.  The definition of
`compactFilteredHull` contains actual filtered diagrams, colimiting cocones, and
 equivalence edges, so it makes no choice from a mere existence proposition and is not a
hollow definition.

Edge cases checked: `IsKappaFiltered` quantifies over the empty simplicial set, so the
filtered index is nonempty as required; `HasSmallColimits` includes the empty diagram,
so the hull conclusion includes the initial object; `κ = ℵ₀` is allowed by
`Cardinal.IsRegular`; the ambient quasicategory and the predicate may be empty; and an
object already in `P` is covered by the explicit one-object presentation clause.  The
poset presentation includes an explicit quasicategory witness after universe lifting.

Searches for an existing declaration were performed before writing.  `msearch.py Q50
lem-coef-accessible-ind-colimit-extension leanfinder` and `leansearch` queries for the
closure of compact objects under filtered colimits returned only ordinary-category
`IsAccessibleCategory`/`IsPresentable` declarations or simplicial-set finite
presentability, with no coherent infinity-category match.  `msearch.py ... loogle`
queries `"Ind", "colimit"`, `"Ind", "IsAccessibleCategory"`, and
`CategoryTheory.IsAccessibleCategory, SSet.Quasicategory` returned no matching
coherent theorem.  Grep of Mathlib's `AlgebraicTopology/Quasicategory` and the project
for `accessible`, `presentable`, `compact`, and `quasicategory` found no existing
compact-filtered-hull statement.  The existing project definitions in
`Sheaf.CategoryTheory.PresentableInfinityCategory` and
`Sheaf.CategoryTheory.EnhancedDiagramsCones` were inspected and reused exactly.

No `STATEMENT-DISPUTED` issue or node fault was found.  The file compiles cleanly with
`scompile.py` (the only proof placeholder is the expected theorem `sorry`).

## Earlier second reading (a previous round; superseded)

I independently reread the module signature against the node.  The hypotheses match the
node clause by clause: regular κ, ambient presentable input encoded by the supplied
`IsEssentiallySmall`/compactness/colimit assumptions, and repleteness under equivalence.
The hull predicate uses exactly small κ-filtered coherent diagrams, colimiting cocones,
and equivalence to the apex.  The conclusion has accessibility, all small colimits,
ambient inclusion preservation, inclusion of every original compact object, and the
nerve of a small κ-filtered poset presentation.  Empty indexing and κ = ℵ₀ remain
included.  No mismatch was found.

## Second reading by Q50

I read the current node, the complete module, both statement-dependency nodes and their
recorded source modules independently. The earlier second reading above missed a real
hypothesis and is superseded by this reading. The natural-language node is unchanged.
There are no new nodes, dependency repairs, or statement_change records in this delivery.
No maintenance repair note for this item exists in coord/repair-notes.

Source check: the node cites HTT, not Stacks. I downloaded the cited Harvard HTT.pdf
(April 9, 2017 printing) into the item's scratchpad and read Definition the project server,
Propositions the project server and the project server--11, Theorem the project server(4), Proposition the project server,
and the compact-hull argument in Lemma the project server, printed p. 480. In particular,
the project server assumes presentable source and target. The small model of E_0 obtains
κ-small colimits from the ambient presentable category; its Ind completion is
presentable by the project server(4). No extra uncountability condition is imposed by the
Ind or cofinal-poset results. The uncountable rank selected for the particular
arrow-category application in the project server is not a hypothesis of this general hull lemma.
Source: https://people.math.harvard.edu/~lurie/papers/HTT.pdf .

Object, hypothesis and conclusion checklist, with the Lean open:

1. Smaller and containing universes: `universe u v`, `κ : Cardinal.{u}`, and
   `E : SSet.{max (u + 1) v}` implement the recorded universe containment without
   identifying u with v. Smallness is always `IsSmall.{u, max (u + 1) v}`.
   Verdict: matches.
2. Infinite regular κ: `hκ : κ.IsRegular`; Mathlib's regularity includes infinitude.
   Verdict: matches, including ℵ₀.
3. Presentable infinity category E: `[hE : SSet.Quasicategory E]` gives only the
   quasicategory. The worker omitted presentability. I added
   `hEpresentable : IsPresentable.{u, v} E`, using the dependency's exact predicate.
   Verdict: repaired. This is a repair of the Lean to the existing node, not a
   correction of the node. Without it, take E empty and P false: all four worker
   hypotheses hold vacuously but its hull cannot have an initial object.
4. E_0 as a full subcategory: `P : E _⦋0⦌ → Prop` and
   `Enhanced.fullSubcomplex E P`. I opened the dependency's construction: its
   simplices are exactly those with every vertex in P. Verdict: matches.
5. E_0 essentially small: `hPsmall : IsEssentiallySmall ...`. This is the recorded
   equivalence to a small quasicategory with coherent quasi-inverse, not cardinal
   smallness of all ambient vertices. Verdict: matches.
6. E_0 replete: `hPreplete` tests an actual `Enhanced.IsEquivalenceEdge` and gives
   the iff between membership at its two endpoints. The dependency's equivalence
   edge carries both inverse triangles. Verdict: matches.
7. Its objects κ-compact in E: `hPcompact : ∀ x, P x → IsKappaCompact E κ x`.
   I read the dependency: this tests the covariant corepresented coherent functor
   on all small filtered colimiting cocones, including its colimit-existence clause.
   It does not mean ordinary Hom-set presentability. Verdict: matches.
8. E_0 closed under κ-small ambient colimits: `hPcolimit` quantifies over every
   `K` with `IsKappaSmall κ K`, every P-valued coherent map F and every colimiting
   coherent cocone t, and asserts `P t.1.1`. No quasicategory assumption is imposed
   on K. I checked `coconeCategory`: `t.1.1` really is its ambient apex.
   Verdict: matches; no existence hypothesis on a selected colimit is substituted.
9. E_1 is the replete full filtered hull: `compactFilteredHull κ P` uses the
   dependency's full subcomplex, a small κ-filtered quasicategory I, an actual
   coherent P-valued diagram F, a colimiting cocone t, and an equivalence between
   x and its apex. The equations orient the edge from x to the apex, exactly as
   in the dependency's accessibility predicate; inverse equivalence makes this
   equivalent to the node's phrasing. I corrected the helper docstring, which
   had described the opposite orientation. Its construction is real data, with
   no sorry or choice from an undetermined existence theorem. Verdict: matches.
10. E_1 κ-accessible: the existential `hE1` supplies its quasicategory instance,
    and `@IsKappaAccessible ... hE1 κ` gives precisely local smallness, filtered
    colimits and an essentially small compact generating subcategory.
    Verdict: matches.
11. All small colimits in E_1: `HasSmallColimits ... (compactFilteredHull κ P).toSSet`
    ranges over every small simplicial indexing set. Verdict: matches.
12. Closure under all small ambient colimits: I added the explicit conjunct
    beginning `∀ (K : SSet...), IsSmall ... K → ∀ (F : K ⟶ E), ...`.
    Every vertex of F is represented by a hull vertex, and the apex of every
    ambient colimiting cocone is represented by a hull vertex. This spells out
    a clause already implied mathematically by repleteness, internal colimits
    and preservation; it makes the node's closure clause directly reviewable.
    Verdict: matches, including the empty diagram.
13. Inclusion preserves all these colimits: `PreservesColimitsIn ... .ι
    (fun I _ _ ↦ IsSmall ... I)`. I opened its definition: this is the actual
    postcomposition of each internally colimiting cocone, not existence of an
    unrelated ambient cocone. Verdict: matches.
14. Every E_1 object has a small κ-filtered poset presentation: the final universal
    quantifier over hull vertices supplies `A : Type u`, `hA : PartialOrder A`,
    its actual `posetNerve`, quasicategory and κ-filtered witnesses, a diagram
    from its explicit lift into E, P-valued vertices, a colimiting cocone and an
    equivalence to its apex. The helper merely binds the order instance and calls
    Mathlib's `CategoryTheory.nerve`; it defines no competing nerve construction.
    Nerve filteredness is the upper-bound condition on all κ-small subsets by
    HTT Example the project server. Verdict: matches, with the small index universe retained.
15. Every E_0 object belongs to E_1: `∀ x, P x → ∃ y : ... _⦋0⦌, y.1 = x`.
    Full-subcomplex vertices are ambient vertices with their membership proof,
    so this is membership, without any skeletal or equality restriction on E.
    Verdict: matches.

Edge cases: empty K occurs in both closure hypotheses and conclusions, and in
HasSmallColimits, so the initial object is included. By contrast an empty filtered
index is impossible because IsKappaFiltered tests the empty simplicial diagram.
The one-object index presents any object already in P. With presentability restored,
E cannot be empty and P cannot be empty: the initial ambient colimit forces an
initial object into P. The worker report's assertion that the empty ambient category
was allowed was therefore wrong. The terminal category with P all objects is allowed.
If E is pointed, its zero object is its initial object and is in P and the hull.
There are no schemes, degrees n, or characteristic restrictions in this lemma.
`Cardinal.isRegular_aleph0` confirms that κ = ℵ₀ is included. `Type u` for the poset
and explicit `uliftFunctor` for its nerve cover the recorded two-universe convention.
No additional smallness, Noetherian, finiteness or field hypotheses occur.

Independent searches, using words different from the worker's main queries:

- `msearch.py ... leanfinder "A replete full subcategory generated by kappa filtered
  colimits of compact objects is closed under colimits"`: ordinary-category
  ObjectProperty colimitsCardinalClosure and presentability results only.
- `msearch.py ... loogle '"Ind", "FullyFaithful"'`: ordinary Ind.inclusion and
  Ind.yoneda, with `Category` and set-valued presheaves, not coherent categories.
- `msearch.py ... leansearch "The Ind completion of a small infinity category with
  kappa small colimits is presentable"`: ordinary IsCardinalLocallyPresentable,
  HasColimits (Ind C), and IndObjectPresentation; no exact coherent match.
- `msearch.py ... grep '[Cc]ompact.*[Ff]iltered|[Ff]iltered.*[Cc]ompact|[Ii]nd.*[Qq]uasi'
  AlgebraicTopology`: zero hits. Direct rg covered Mathlib's Quasicategory and
  Presentable directories, upstream WeilConjectures/CategoryTheory, all project
  Sheaf for the declaration/helper names, and dag/lean_names_upstream.json.
  I also opened Mathlib's nerve and preorder-category definitions.
- The project has `SSet.Presentability.exists_compactGeneratedFilteredHull` in
  `InfinityCompactGeneratedFilteredHull.lean`. I read its full signature and
  corresponding node: it constructs a minimal colimit hull of an arbitrary small
  family G and an existential family A of compact generators. It neither fixes
  the supplied essentially small κ-small-colimit-closed E_0 nor identifies its
  specified filtered hull or supplies its poset presentations. It is not an
  existing declaration of this node or its helper definition.

Repairs: restored the missing ambient-presentability hypothesis; made the ambient
closure clause explicit; corrected the helper's edge-orientation docstring; expanded
its statement docstring into all six current DAG proof steps with their node names.
Both public dependency imports are used. The three additional proof-dependency
statement nodes have no recorded Lean declarations, so no proof-only import exists
for them yet; there is no dependency module to add merely for a future proof.
The helper definitions belong to this node's own hull and poset-presentation notion
and are listed in lean.declarations. No independent definition is introduced.
All theorem proofs remain sorry, and neither helper has hollow data.

Validation: the prescribed scompile.py compiled the delivered file cleanly, both its
sandbox and library forms (1.5 s and 1.7 s). The initial invocation from the shared
read-only directory had no sandbox source path; rerunning from the item's writable
sandbox succeeded. I checked that every variable and universe is explicitly bound,
that all Lean lines have at most 100 characters, and that lean.statement is the
verbatim theorem signature. No non-Lean node field was changed.
