## Worker report

The module defines `PreservesKappaCompactObjects`, the core-enriched subcomplexes
`PrLSubcomplex` and `PrRSubcomplex`, their simplicial sets `PrL` and `PrR`, and the
statement `SSet.Presentability.compact_model_pr_duality`. `PrL` has presentable
vertices and arrows preserving all small colimits and κ-compact objects. `PrR` has
the same presentable vertices and arrows preserving small κ-filtered colimits and
carrying an explicit coherent left adjoint (`ModelInfinity.CoherentAdjunction`).
The theorem states the adjunction compactness/filter-colimit equivalence, existence
of right adjoints for colimit-preserving maps, an equivalence of the left/right
subcategories, coherent diagram correspondence, and the Ind equivalence with the
κ-small-colimit subcategory. Every proof is `sorry` as required for stage 2.

The first theorem clause binds quasicategories `C,D`, assumes their recorded
`IsPresentable` predicates, a coherent adjunction `L ⊣ R`, and states the exact
compactness/filtered-colimit biconditional; its second conjunct states right-adjoint
existence for every small-colimit-preserving `L`. The second clause gives a coherent
functor equivalence `PrL ≃ (PrR)^op`. The third clause quantifies a small coherent
index `S`, a diagram into `PrL`, and a diagram into `PrR` with identical underlying
category values under reversal. The final clauses give mutually quasi-inverse
coherent functors between the κ-small-colimit category (`compactRex`) and `PrL`,
with the forward object equation identifying the value with `indKappa`.

Dependencies used: `Sheaf.CategoryTheory.PresentableInfinityCategory` for
`IsPresentable`, `IsKappaCompact`, `IsKappaAccessible`, `IsKappaFiltered`,
`IsSmall`, and `PreservesColimitsIn`; `Sheaf.CategoryTheory.EnhancedDiagramsCones`
for `IsFunctorEquivalence`; `Sheaf.CategoryTheory.IndKappaPresentability` for
`indKappa`; `Sheaf.CategoryTheory.SmallRightAdjointDiagramCompactModel` for
`compactRex`; `Sheaf.CategoryTheory.EnhancedCartesianFibration` for `CatInfinity`
and core subcomplexes; and `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`
for coherent adjunctions.

Edge cases checked: κ is explicitly uncountable and regular; the empty indexing
simplicial set is included by `IsSmall`/`IsKappaFiltered`; empty and terminal
quasicategories are allowed; the compact-object predicate quantifies all vertices;
all higher simplices are retained by the subcomplex map field. Universe levels use
`max (u + 1) v` for category values and `max (u + 2) (v + 1)` for their coherent
functor simplicial sets.

Searches made: `msearch.py Q125 lem-coef-compact-model-pr-duality leanfinder
"compact objects Ind equivalence presentable infinity categories left right adjoints coherent"`
returned only ordinary-category presentability declarations; `loogle` for
`CategoryTheory.Ind`, `PrL`, and `PrR` returned no infinity-category match; grep of
Mathlib `CategoryTheory/Presentable` and the project `WeilConjectures/` found no
matching infinity-category subcategories. Grep of `lean/Sheaf` found the published
`CatInfinity`, `compactRex`, `indKappa`, and coherent-adjunction interfaces used here.
No exact existing declaration of this statement was found.

## Earlier second reading (a previous round; superseded)

The module and node were read independently. The recorded hypotheses use the same
small universe, uncountable regular κ, presentability assumptions, coherent adjunction,
and preservation clauses as the source. `PrL` and `PrR` retain all higher simplices of
`CatInfinity` while imposing exactly the stated arrow conditions. The equivalence and
Ind clauses use coherent `IsFunctorEquivalence`; the object equation identifies the
forward functor with `indKappa`. No additional mathematical hypothesis was introduced.


## Second reading by Q125

I independently read the item node, its eight proof steps, all four original
statement dependencies and their recorded Lean signatures, the delivered module,
and the existing helper interfaces used below. The earlier short reading above
is superseded by this one. The natural statement is correct and unchanged; the
first worker's Lean did not yet render all of it.

Source checked directly: Lurie, Higher Topos Theory, at
https://www.math.ias.edu/~lurie/papers/HTT.pdf (the node's source host contains an
inherited typo). In particular I read Definition the project server, Proposition the project server,
Definition the project server, Notation the project server, Proposition the project server, Remark the project server,
Proposition the project server, and the surrounding Definitions the project server--2,
Proposition the project server, Corollary the project server and Corollary the project server. There is no
Stacks source place for this item. The surrounding source assumes a small
universe inside a containing universe, fixed regular rank, and compactly
generated means BOTH presentable and accessible at that rank. The uncountable
rank removes the idempotent-completeness qualification on the small side.

Object/hypothesis/conclusion checklist (my statement inventory and Lean match):

1. Small universe U inside U', then Cat-infinity in a further universe:
   `u`, `max (u + 1) v`, and `max (u + 2) (v + 1)` respectively.
   `Enhanced.CatInfinity` is the existing core-enriched coherent nerve, not
   the nerve of an ordinary category or a functor object with noninvertible
   transformations as mapping-space edges. Verdict: exact.
2. Uncountable regular rank lambda in U: `κ : Cardinal.{u}`, `hκ : κ.IsRegular`,
   `hκu : Cardinal.aleph0 < κ`. Mathlib regularity includes infinitude.
   Verdict: exact; no claim at κ = aleph0 is made.
3. PrL objects presentable AND κ-accessible: the first predicate in
   `PrLSubcomplex.obj` now conjoins `IsPresentable.{u, v}` and
   `IsKappaAccessible.{u, max (u + 1) v}` for each enriched vertex.
   Verdict: repaired; fixed-rank accessibility was missing.
4. PrL arrows preserve all small colimits and κ-compact objects:
   `PreservesColimitsIn f (fun I _ _ ↦ IsSmall ... I)` and
   `PreservesKappaCompactObjects κ f`. The latter quantifies every vertex
   and uses the dependency's mapping-space compactness predicate.
   Verdict: exact; these parts of the first worker's definition are retained.
5. PrR has those SAME objects: its object predicate has the same conjunction.
   Its arrows satisfy the existing `PreservesKappaFiltered` predicate and admit
   `L` with `Nonempty (ModelInfinity.CoherentAdjunction L f)`.
   Verdict: accessibility repaired; the original coherent-adjunction arrow
   condition was correct and is retained.
6. Clause (1), given C,D objects and L adjoint to R: the theorem binds
   quasicategories C,D, both presentability and both rank-accessibility
   predicates, then universally quantifies L,R and assumes their existing
   coherent adjunction. Its conclusion is precisely
   `PreservesKappaCompactObjects κ L ↔ PreservesKappaFiltered κ R`.
   Verdict: repaired the missing rank hypotheses, without strengthening the node.
7. Clause (1), every small-colimit-preserving L has a right adjoint: the
   SECOND conjunct under C,D is now a separate `∀ L`, with only colimit
   preservation before `∃ R, Nonempty (CoherentAdjunction L R)`.
   Verdict: repaired the old quantifier scope, which assumed an adjunction
   before concluding existence and therefore failed to express this clause.
8. Clause (2), adjoint reversal equivalence: `Nonempty (PrAdjointDuality κ)`
   supplies an actual simplicial map `(PrL κ).op → PrR κ` and
   `Enhanced.IsFunctorEquivalence`. This is the opposite form of the node's
   `PrL → (PrR).op` equivalence, with identical mathematical variance.
   `objects` identifies the underlying category values, and `adjunctions`
   says the actual reversed edge, transported by those SAME object equations,
   is right adjoint to the original edge. Verdict: repaired; the old bare
   equivalence did not require either identity on objects or adjoint arrows.
9. Clause (2), all small coherent diagrams with same values and right-adjoint
   arrows: precompose `rightAdjoints` with the opposite of any diagram F.
   `objects` and `adjunctions` give its required values and arrows. The inverse
   and the natural inverse equivalences in `isEquivalence` give the inverse
   correspondence up to coherent equivalence. These are whole simplicial
   maps, so every higher simplex and its compatibility is carried along.
   Verdict: exact consequence of the normalized equivalence, not a separate
   unconnected existence assertion about diagrams with equal vertices.
10. Clause (3), the small κ-cocomplete category: reuse `compactRex`,
    `compactRexValue` and their underlying `compactRexSubcomplex` from
    `Sheaf.CategoryTheory.SmallRightAdjointDiagramCompactModel`. I opened the
    definitions: every κ-small simplicial shape is tested, the empty shape
    included; mapping vertices preserve those colimits, and the ambient mapping
    spaces are cores. Verdict: exact; no duplicate small-category notion.
11. Clause (3), Ind is the equivalence, not an arbitrary one: the structure
    `PrCompactModelDuality` contains `ind` and `compact`, with coherent
    `left_inverse` and `right_inverse` comparisons. `models` reuses the existing
    `CompactIndModel`, whose equivalence targets the actual `indKappa` full
    presheaf subcategory, and whose `yoneda_comparison` identifies its Yoneda
    map with the already constructed Yoneda functor through the actual inclusion.
    These models express the source's construction up to coherent equivalence.
    Verdict: repaired; the old forward object equality alone was insufficient.
12. Forward arrows are the filtered extensions of j_D u:
    `extensions` requires `PreservesKappaFiltered` of the actual induced arrow
    and the coherent equation between `j_C` followed by that arrow and the
    lifted small arrow followed by `j_D`. The small-arrow domain and the two
    model Yoneda maps use the existing universe lifts. Verdict: repaired;
    this entire arrow normalization was absent.
13. Reverse values are SMALL models of the FULL compact subcategory:
    `compactModels` maps the lifted small value of `compact` into the EXISTING
    `compactObjects` full subcomplex; `compactModels_equivalence` makes it an
    equivalence. I opened `AccessibleCompactSliceDensity.compactObjects`,
    which is `fullSubcomplex C (IsKappaCompact C κ)`. The landed owning node
    is added to `stmt_deps`; its dependency closure does not contain this item.
    Verdict: repaired; the old reverse functor had no compact-object condition.
14. Reverse arrows are restrictions of the original arrows:
    `restrictions` compares the actual lifted arrow of `compact`, followed by
    the target compact model and inclusion, with the source compact model and
    inclusion followed by the original arrow. `compactRexDiagramArrow` contains
    only the canonical endpoint transports from simplicial naturality and the
    existing edge extractor, with real data and no postponed proof.
    Verdict: repaired; this restriction clause was absent.
15. Yoneda identifies C with all compacts of Ind(C): `yoneda_compacts` supplies
    a factorization of the SAME model Yoneda map through the full compact
    subcomplex, with the factor an `IsFunctorEquivalence`. Verdict: repaired;
    this final conclusion was absent.
16. All higher diagram data: `ind`, `compact`, and `rightAdjoints` are actual
    maps of coherent nerves; the inverse comparisons are edges in the full
    internal functor simplicial sets. Whiskering them works for any coherent
    index, retaining every simplex. Verdict: exact; no passage to just the
    homotopy category or an edgewise diagram is used.

Dependency interfaces read: `PresentableInfinityCategory.IsPresentable` is
accessibility at SOME rank plus all small colimits, so it does not supply
`IsKappaAccessible` at the stated rank. `IsKappaCompact` includes existence of
filtered colimits and preservation by the actual corepresented functor, not an
ordinary categorical Hom test. `EnhancedDiagramsCones.IsFunctorEquivalence`
contains an actual coherent quasi-inverse and two natural equivalences.
`EnhancedCartesianFibration.CatInfinity` restricts every mapping simplex to the
core. `IndKappaPresentability.indKappa` is the full replete subcategory of
space-valued presheaves on small κ-filtered colimits of representables, and its
Yoneda map is the restriction of the constructed Yoneda functor. I also opened
`InfinityYonedaEvaluation.Yoneda.yoneda`: the comparison in `CompactIndModel`
uses precisely that constructed Yoneda after universe transport.
`ModelInfinityDerivedAdjunction.CoherentAdjunction` contains coherent units,
counits, triangle simplices and universal comma objects. No ordinary-category
adjunction, arbitrary chosen functor, or weaker compactness predicate is used.
The helpers imported from the already landed small-right-adjoint module are
used only as existing definitions; its downstream theorem is not invoked.

Edge cases: empty test diagrams ARE included in κ-filteredness and force a
filtered indexing category to be nonempty; the empty indexing category itself
is NOT treated as filtered (the earlier report's wording was misleading).
Empty colimits ARE included in the small κ-cocomplete category and colimit
preservation. The empty quasicategory is not falsely declared presentable,
since it has no empty colimit. The terminal category and zero/initial objects
are covered, without nonzero/nonempty object assumptions. Identity and
constant diagrams, degenerate simplices and dimension zero are included in
the actual subcomplex definitions and canonical endpoint transports. There
is no field, scheme, characteristic or numerical degree in this statement.
The containing universe v is independent of u; it is never equated to u.

Independent searches: `msearch.py ... leanfinder` with the new query
"Ind completion equivalence compact subcategory presentable quasicategories
adjoint duality" returned ordinary `CategoryTheory.Ind` and
`CategoryTheory.Ind.leftExactFunctorEquivalence`, not this theorem.
`msearch.py ... loogle '"IsFunctorEquivalence"'` returned no match.
I searched Mathlib, the source WeilConjectures tree and lean/Sheaf for
`PrL`, `PrR`, `PreservesKappaCompact`, `compact_model_pr_duality` and
`compactObjects`; the last found the existing full compact subcategory used
above, and none found an existing Pr duality statement. I opened Mathlib's
`CategoryTheory/Presentable/Adjunction.lean`: its nearest compactness lemma
is about ordinary categories and set-valued Hom. It cannot replace the
quasicategorical biconditional or the normalized coherent equivalences.
Searches for the new helper and structure names found no conflicts.

Other repairs: the proof docstring now follows all eight DAG steps, including
compact-stage retracts and size, compact detection, both bifibration lift
constructions, the naturality/Yoneda inverse argument, the use of uncountability,
coherent extension/restriction and the normalized quasi-inverse. Added the
available proof-dependency module imports as the stage-3 proof plan. All
existing correct compactness, core-enrichment and coherent-adjunction
constructions were reused. No new DAG definition nodes, dependency module
repairs, natural statement changes, target edits or proved theorems are in
this delivery. Every theorem proof remains exactly `by sorry`.

Validation: the repaired module compiled cleanly through `scompile.py` in both
the isolated sandbox and its library module path. The required `deliver2.py
--no-push` returned OK: server preflight passed and the module compiled.
The node's `lean.statement` is verbatim the final theorem signature; maximum
Lean line length is 97 characters and the only `sorry` is its named theorem.
