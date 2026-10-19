## Worker report

The item is stated in `lean/Sheaf/CategoryTheory/ColimitSubdiagramApproximation.lean` as
`SSet.Enhanced.colimit_subdiagram_approximation`. It introduces an uncountable regular
cardinal `κ`, a small simplicial set `K`, a quasicategory `C` admitting all small
colimits, a coherent diagram `p`, chosen colimiting cocones `q L` for every
`L : kappaSmallSubdiagrams κ K`, and a colimiting cocone `l` on `p`. The conclusion
asserts universe-smallness of the poset, κ-filteredness of its nerve, and the coherent
incidence diagram, compatible local cocones, global colimiting cocone, and triangle of
homotopies. The empty subset is represented by the subcomplex order and no nonempty
hypothesis is placed on `K`; the `K = ∅` and `K` itself κ-small cases are therefore
included.

The hypotheses and clauses render as follows.

* `κ` is `Cardinal.{u}`, `hκ : Cardinal.aleph0 < κ` is the uncountability bound, and
  `hκreg : Cardinal.IsRegular κ` is regularity.
* `K : SSet.{u}` and `C : SSet.{max u v}` are the small shape and ambient quasicategory;
  `[Quasicategory C]` is the horn-filling hypothesis.
* `hcolimits` gives, for every small simplicial shape and coherent diagram into `C`, a
  cocone vertex satisfying `IsColimiting`.
* `p : SSet.uliftFunctor.obj K ⟶ C` is the coherent diagram.
* `q` supplies one cocone vertex for every κ-small subcomplex, and `hq` says each is
  colimiting for the restricted diagram.
* `l` and `hl` are the arbitrary global colimiting cocone required by the statement.
* `Small (kappaSmallSubdiagrams κ K)` and
  `IsKappaFiltered κ (nerve (kappaSmallSubdiagrams κ K))` state the size and filteredness
  clauses. The latter is the landed `SSet.Presentability.IsKappaFiltered` predicate and quantifies over
  every κ-small coherent diagram, including the empty one.
* The existential `c`, `a`, and `ν` uses `directedCoverIncidence`,
  `directedCoverToShape`, `directedCoverToIndex`, and `directedCoverFiber` from
  `Sheaf.CategoryTheory.DirectedCoverColimitAssembly`. The first conjunction identifies
  every stage apex with `q L`; the next two identify the two boundary restrictions of
  `a`; the fiber conjunction identifies each local cocone; `IsColimiting c ν` and
  `ν.1.1 = l.1.1` give the compatible colimiting cocone and comparison equivalence; the
  final existential `t` is the coherent triangle with its three face equations.

The dependency declarations used are:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations in `SSet.Enhanced` such
  as `coconeCategory`, `IsColimiting`, and the simplicial primitives.
* `Sheaf.CategoryTheory.FinalIndexColimit`, declaration
  `SSet.Enhanced.coconeHomotopy`, re-exported by the directed-cover module.
* `Sheaf.CategoryTheory.DirectedCoverColimitAssembly`, declarations
  `SSet.Enhanced.directedCoverIncidence`, `directedCoverToShape`,
  `directedCoverToIndex`, and `directedCoverFiber`.
* `Sheaf.CategoryTheory.PresentableInfinityCategory`, declarations listed in its node
  record, with `SSet.Presentability.IsPresentable` as the principal declaration. This module uses
  `SSet.Presentability.IsKappaSmall` and `SSet.Presentability.IsKappaFiltered` directly.
* Mathlib's `SSet`, `SSet.Subcomplex`, `SSet.nonDegenerate`, `SSet.nerve`, and
  `SSet.Quasicategory` (the latter's nerve instance is imported from
  `Mathlib.AlgebraicTopology.Quasicategory.Nerve`).

I checked the edge cases explicitly against the definitions: the bottom subcomplex is
present in the subdiagram poset, the empty simplicial set has no nondegenerate
simplices, a κ-small `K` is itself a stage, and the conclusion has no condition that
excludes `K = ∅`. The incidence construction and all face equations remain well-typed
in those cases.

The searches made were:

* `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q29 lem-coef-colimit-subdiagram-approximation leanfinder "In an infinity category the colimit of a small simplicial diagram is a kappa filtered colimit of the colimits of its kappa small simplicial subsets"`: eight ordinary Mathlib hits, no matching infinity-categorical assembly theorem.
* `... msearch.py ... loogle '"colimit", "Subcomplex"'`: three `SSet.Subcomplex`/ordinary filtered-colimit hits; none states the required coherent assembly.
* `... msearch.py ... grep 'subdiagram|Subcomplex.*[Cc]olimit|[Cc]olimit.*Subcomplex|small.*sub.*diagram' CategoryTheory`: no match.
* `rg -n 'subdiagram|Subcomplex.*[Cc]olimit|[Cc]olimit.*Subcomplex'` in the source and `lean/Sheaf`: no existing project declaration for this statement; the only relevant declaration is the recorded directed-cover assembly used above.
* The previous attempt found no recorded presentability interface. The current node
  now records NU’s landed `SSet.Presentability` interface, which this packet imports.

The theorem proof is intentionally `sorry`, as required for stage 2. No statement is
marked `STATEMENT-DISPUTED`.

## Saved-packet repair and self-check

On 2026-10-17 I ran the required dry run before changing the saved packet. The
current dependency node now records NU’s complete module
`Sheaf.CategoryTheory.PresentableInfinityCategory` in namespace
`SSet.Presentability`. The saved packet's dependency module predates that landing
and included incorrect placeholder notions (notably compactness independent of
its object). I removed that duplicate module and node copy, and used the landed
`IsKappaSmall` and `IsKappaFiltered` directly. No natural-language node statement
changes. The bounded-subdiagram definition and order instance remain real data.
All three declarations are listed in the item's Lean record and have source tags.

The original self-check covered the same assembly equations and empty-shape
cases. I re-read those equations against the current directed-cover module and
checked that the only interface changes are the two qualified presentability
predicates. The final packet has only the item module and its node record.

The repaired file passed `scompile.py` with no errors or warnings. A fresh name
search in the current source and `lean/Sheaf` found no existing
`kappaSmallSubdiagrams` or `colimit_subdiagram_approximation`. The sandbox node
matches the current repository node in every field except `lean`; its declaration
list contains both helpers and the theorem. Every Lean line has at most 100
characters and `autoImplicit` is disabled.

I opened [HTT](https://www.math.ias.edu/~lurie/papers/highertopoi.pdf), printed
pp. 249–253, and checked Remark the project server, Corollary the project server and the proof of
Corollary the project server. The last proof uses the directed poset of bounded simplicial
subsets and its union; its extra cardinal bound only bounds that poset's size,
which this node does not assert.

An independent second reading remains for the dispatcher’s separate reader.

## Second reading by Q29

I independently opened the item node, every statement dependency, the directed-cover
proof dependency and their source declarations. The item cites HTT, not Stacks:
I read the March 10, 2012 PDF at
https://www.math.ias.edu/~lurie/papers/highertopoi.pdf, §4.2.3's standing setup,
Proposition the project server and its proof, Remark the project server, Corollary the project server and the proof
of Corollary the project server (printed pp. 248–253). There is no additional finiteness,
local-smallness or categorical hypothesis in that setup. Proposition the project server
first extends the prescribed partial cocones and then gives a trivial fibration
on cocone categories for that fixed extension; Corollary the project server identifies its
colimits with the colimits of the restriction to the index nerve. The stronger
outer cardinal relation in the project server is used to bound the indexing poset's cardinal,
which this node expressly does not require. No repair note exists for this item.

My object/hypothesis/conclusion list, matched to the final Lean, is:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Fixed small and containing universes | `universe u v`, `K : SSet.{u}`, `C : SSet.{max u v}`, degreewise `SSet.uliftFunctor.{v}` | Correct: no equality imposed on the shape and ambient universes. |
| Uncountable regular small cardinal κ | `κ : Cardinal.{u}`, `hκ : Cardinal.aleph0 < κ`, `hκreg : Cardinal.IsRegular κ` | Exact hypotheses. |
| Small simplicial shape K | `K : SSet.{u}` | No category, nonemptiness, finite-dimension or cardinal bound on K assumed. |
| Quasicategory C admitting all small colimits | `[Quasicategory C]`, `hcolimits` over every `L : SSet.{u}` and lifted diagram | Exact; arbitrary simplicial shapes are tested. No accessibility or presentability assumption. |
| Coherent diagram p | `p : SSet.uliftFunctor.{v}.obj K ⟶ C` | The recorded coherent functor is a simplicial map, not an ordinary functor. |
| Poset of subdiagrams with fewer than κ nondegenerate simplices | `kappaSmallSubdiagrams κ K := {L : K.Subcomplex // SSet.Presentability.IsKappaSmall κ L.toSSet}` and `PartialOrder.lift Subtype.val Subtype.val_injective` | Correct bounded subtype and actual inclusion order. |
| Index poset small | `Small.{u} (kappaSmallSubdiagrams κ K)` | Correct universe-smallness, without cardinal < κ. |
| Nerve κ-filtered | `SSet.Presentability.IsKappaFiltered κ (nerve (kappaSmallSubdiagrams κ K))` | Correct landed definition; the Mathlib poset-nerve instance gives its quasicategory structure. |
| Chosen partial colimiting cocones | `q` in the cocone category of `SSet.uliftFunctor.map L.1.ι ≫ p`, `hq` its `IsColimiting` predicate | Exact cocones, not merely chosen apices or existential colimits. |
| One coherent assembled diagram Q, with Q(L) = q_L | Existential `c`, its vertex equation `c.app ... = (q L).1.1` | Correct after quantifier repair: c is fixed before any global cocone. |
| Coherent transitions respecting the specified partial cocones | Existential incidence transformation `a`, endpoint equations using `directedCoverToShape` and `directedCoverToIndex`, and fiber equation equaling `coconeHomotopy ... (q L)` | Retains each entire local cocone, its apex, and higher chain compatibility. |
| For any colimiting cocone p → c | Inner `∀ (l : (coconeCategory p) _⦋0⦌), IsColimiting p l → ...` | Exact quantifier order after repair. |
| Compatible colimiting cocone Q → c | `∃ ν`, `IsColimiting c ν`, `ν.1.1 = l.1.1` | Same apex as the specified global cocone and an actual coherent colimit. |
| Compatibility with that specified global cocone | `∃ t : incidence ⊗ Δ[2] ⟶ C`, faces δ2 = a, δ0 = pulled-back `coconeHomotopy c ν`, δ1 = pulled-back `coconeHomotopy p l` | The triangle witnesses composition compatibility; the common apex identifies the comparison with an equivalence. |
| Empty subset and empty K included; no κ-bound on the index | No nonempty binder on K or its subcomplexes and no `IsKappaSmall` assertion on the index nerve | Exact clauses. |

Dependency checks: Mathlib `SSet.Subcomplex` is `Subfunctor K`, `toSSet` is the
restricted simplicial functor, and `nonDegenerate n` is the complement of the
specified degeneracy images. The landed `IsKappaSmall` counts
`Σ n : ℕ, S.nonDegenerate n` via `HasCardinalLT`, not all simplices or vertices
alone. `IsKappaFiltered` asks for an actual cocone for every κ-small simplicial
diagram, including the empty shape. I read `Enhanced.coconeCategory` as the
recorded coherent comma construction and `IsColimiting` as its initial-object
predicate. `coconeHomotopy` extracts the entire coherent transformation from
that cocone vertex. I read all four directed-cover helpers: the incidence set
contains simplex/chain pairs whose simplex belongs to every chain stage; its
two maps are projections, and its fiber uses the constant chain at L. No private
copy or weakened dependency interface is used. This delivery contains no new
node, dependency module or statement_change, so H12/H13 and the corrected-node
citer audit do not apply.

Edge cases: the empty subcomplex has zero nondegenerate simplices and belongs
to the index since κ is uncountable. If K is empty, this is its only subcomplex;
the incidence object is empty and the conclusion compares initial objects.
If K is κ-small, its top subcomplex is a greatest stage. Dimension zero is included:
every vertex is nondegenerate, and a κ-small test diagram has fewer than κ vertices.
The empty test diagram has the empty union as an upper bound. There is no scheme,
coefficient ring, characteristic or degree parameter to restrict; a quasicategory
with a zero object is covered without a nonzero assumption. The ambient universe
is independent of u, and lifting changes no simplex or cocone data. The index is
`Type u`, so the diagram is small enough for exactly the assumed colimits.

Independent H4 searches, using different wording from the first reader:

- `msearch.py Q29 lem-coef-colimit-subdiagram-approximation leansearch
  "Every colimit in a quasicategory is a filtered colimit of colimits of small simplicial subsets"`:
  eight results on ordinary colimits, filtered categories and `SSet.hasColimits`; no match.
- `msearch.py ... leanfinder
  "A simplicial diagram is the filtered union of its cardinal bounded subcomplexes and its colimit is the colimit of their colimits"`:
  eight results, principally ordinary subcomplex multicoequalizers and finite colimits; no coherent assembly theorem.
- `msearch.py ... loogle '"Subcomplex", "colimit"'`: three ordinary subcomplex
  colimit results, none with coherent prescribed cocones in a quasicategory.
- `rg -n -i 'kappasmallsubdiagrams|colimit_subdiagram_approximation|bounded simplicial|colimits.*simplicial subsets|subcomplex.*filtered'`
  over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, its Mathlib tree and
  repository `lean/Sheaf`: only ordinary preservation of filtered colimits by
  `Subcomplex.toSSetFunctor` and an unrelated algebraic-geometric complex.
  A DAG/upstream-name search also found the item and its citer, with no recorded
  duplicate bounded-subdiagram definition or theorem. The ordinary Mathlib
  results concern colimits in SSet, not colimits of diagrams into arbitrary C.

Mismatch repaired: the original theorem bound `l` and `hl` before `∃ c a ν`,
allowing the assembled diagram and transition data to depend on the global
colimit cocone. The node says to assemble the chosen partial cocones first,
then to give a compatible colimit for any global cocone. I removed those outer
binders and placed `∀ l, IsColimiting p l → ∃ ν, ...` after the fixed c/a and
local-cocone clauses. The node's mathematical statement is unchanged. I expanded
the proof docstring through all four node steps, including the arbitrary-global-
cocone lifting argument from the source, and copied the revised signature
verbatim into `lean.statement`. All other correct declarations were retained.

The two helper declarations contain real data; the only postponed result is the
named theorem, with `by sorry`. Every declaration has its source and blueprint
tag, all Lean lines are at most 100 characters, and all variables/universes are
bound with auto-implicit disabled. The repaired module passed `scompile.py`
for both sandbox and library contexts without errors or warnings.
