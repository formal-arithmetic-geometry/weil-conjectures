## Worker report

The module `Sheaf.CategoryTheory.CompactRelativeCoconeFactorization` states
`SSet.Enhanced.compact_relative_cocone_factorization` with proof `sorry`.  It also
constructs the real endpoint inclusion `intervalEndpoint`, ordered-join map `joinMap`,
and the canonical nerve-cone edge `nerveConeEdge`; these are the explicit maps used in the
four restriction equations.  The module uses `SSet.Subcomplex` for the simplicial subset
`K' ⊆ K`, `Cardinal.mk K.N < κ` for κ-smallness, a partial order with `Nonempty I` and the
upper-bound condition `hI` for the index poset, and the `IsLocallySmall`,
`HasSmallKappaFilteredColimits`, and `IsKappaCompact` predicates from the dependency module.

The hypotheses are rendered as follows.  `hκ` is
`Cardinal.aleph0 ≤ κ ∧ κ.IsRegular`.  `hI` says every `s : Set I` of cardinality below κ
has an upper bound.  `[Quasicategory E]`, `hEsmall`, and `hEcolim` express that `E` is a
locally small quasicategory with all small κ-filtered colimits.  `hK` is the κ-smallness of
`K`; `K' : K.Subcomplex` is the specified simplicial subset.  `q : K ⟶ E` is the diagram,
and `hq` says `IsKappaCompact E κ (q.app _ x)` at every vertex.  `pbar` is the cocone on
`nerve I`, `c` is its apex, `hpbar` is its colimiting-cocone predicate, and `hpapex` identifies
its cone vertex with `c`.  `r` has domain `K' ⋆ N(I)ᵗʳⁱᵃⁿᵍˡᵉ`; `hrK` and `hrI` give its two
specified restrictions.  `u` has domain `K ⋆ Δ⁰`; `huK` gives its `K` restriction and
`huapex` identifies its apex with `c`.  `hur` is the equality of the two restrictions to
`K' ⋆ {∞}`, using `joinMap` and the right-join inclusion.

The conclusion is `∃ i : I, ∃ v : K ⋆ Δ¹ ⟶ E`.  The first conjunct
`orderedJoinInl K Δ[1] ≫ v = q` is the restriction to `K`.  The second conjunct
`orderedJoinFunctor.map (𝟙 K, intervalEndpoint 1) ≫ v = u` is the restriction to
`K ⋆ {1}`, with vertex `1` identified with the cone apex.  The third conjunct
`orderedJoinInr K Δ[1] ≫ v = nerveConeEdge i ≫ pbar` is the edge `pbar(i → ∞)` on
`Δ¹`.  The fourth conjunct
`orderedJoinFunctor.map (K'.ι, 𝟙 Δ[1]) ≫ v = joinMap (𝟙 K') (nerveConeEdge i) ≫ r`
is exactly the required restriction on `K' ⋆ Δ¹`.  No colimit of `q` or of `q|K'` occurs.

The dependency module `Sheaf.CategoryTheory.PresentableInfinityCategory` was added because
`def-coef-presentable-infinity-category` had no recorded Lean declaration or Mathlib match.
It states `IsKappaSmall`, `IsKappaFiltered`, `IsColimitingCocone`, `IsLocallySmall`,
`HasSmallKappaFilteredColimits`, `IsKappaCompact`, `PreservesColimitClass`,
`IsKappaAccessible`, `IsAccessible`, and `IsPresentable`, with the explicit simplicial-set
and ordered-join data used by the item.

Edge cases checked: `I` is explicitly nonempty (the empty-shape filteredness case); `K` and
`K'` may be empty; κ may be `aleph₀`; no assumption that either `q` or `q|K'` has a colimit
is present; `K'` is a genuine subcomplex and all endpoint maps are degreewise simplicial.
The nerve edge is built from `joinPointTopSimplex 0`, so the cases `i` and the cone vertex
are retained without an arbitrary choice.

Searches for an existing declaration were made with:

* `msearch.py Q54 ... leanfinder "A cocone on a small diagram of kappa compact objects ..."`:
  hits were ordinary `IsCardinalPresentable.exists_*` factorization lemmas, not the relative
  simplicial join statement; verdict no match.
* `msearch.py Q54 ... leansearch "A cocone on a kappa small diagram ... relative ..."`:
  hits were ordinary categorical filtered-colimit lemmas; verdict no match.
* `msearch.py Q54 ... loogle "IsCardinalPresentable, exists_hom"`:
  only `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit` and `exists_hom₂...`;
  verdict no match.
* `msearch.py Q54 ... grep "relative.*cocone|cocone.*factor|compact.*cocone"` in Mathlib:
  only unrelated subobject cocones and generic `IsLimit` constructors; verdict no match.
* `rg -n "compact|relative.*cocone|Quasicategory|IsKappa"` in `WeilConjectures/` and
  `lean/Sheaf`: no declaration of this relative factorization statement; only unrelated
  presentability infrastructure was found.

No `STATEMENT-DISPUTED` flag or node correction is needed.

## Dependency modules

`def-coef-presentable-infinity-category`: its node had no `lean` record and no Mathlib
match.  The added `PresentableInfinityCategory.lean` module states the node's smallness,
filteredness, compactness, local-smallness, accessibility, presentability, and colimit
preservation notions, and its copied node changes only the `lean` record with a note
explaining this repair.

## Earlier second reading (a previous round; superseded)

I reread the copied node and both modules.  The cardinal and poset hypotheses are all
explicit; `K'` is a subcomplex of the same `K`; `q`, `pbar`, `r`, and `u` have the exact join
domains in the node.  The four conclusion conjuncts correspond one-for-one to the four
restrictions in the node, with the interval endpoint `1`, the canonical `i → ∞` edge, and
the relative `K'` equality all rendered by actual ordered-join maps.  The dependency module
supplies every notion named by the item and introduces no private replacement for the
simplicial-set primitives.  Compilation with `scompile.py` is clean for the dependency file
followed by the item file.

The final module keeps the smaller and ambient universes separate: `κ : Cardinal.{u}` and
`I : Type u`, while `E`, `K`, and the lifted nerve live in `SSet.{max u v}`.  The helper
`liftedNerve` uses `SSet.uliftFunctor`, so no equality of the small and ambient universes is
assumed.  `liftedNerveInr`, `liftedConeMap`, `coneAgreement`, `relativeStageMap`, and
`relativeRestriction` make each endpoint and restriction map explicit and keep elaboration
stable at the universe boundary.


## Second reading by Q54

This reading supersedes the earlier second-reading paragraph and the descriptions of
superseded dependency predicates in the Worker report. I read the current item node,
its sandbox signature, every statement dependency's recorded signature and source, the
landed presentability module, the prism construction, and the join generator. The item
node's natural-language statement is unchanged. There is no statement_change and no new
node or dependency module in the final delivery.

Source checked directly: [Lurie, Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Corollary the project server (printed p. 401), Proposition the project server (printed p. 60), Proposition
the project server (printed pp. 219--220), and the actual pullback Y and incoming-edge construction
in the proof of Lemma the project server (printed pp. 479--480; PDF pages 496--497). This node has
no Stacks source or Stacks .tex place. The ambient lemma assumes an uncountable regular
cardinal to carry out its countable recursive common-refinement construction. This
node isolates one relative finite-stage extension: compactness of the two coslice
fibrations, filtered preservation of the homotopy pullback, and edge extraction use only
an infinite regular cardinal. The outer countable recursion and its uncountability
hypothesis are not part of this node. Likewise, this node only needs the stated
κ-filtered colimits, as in Corollary the project server, rather than every filtered colimit.

Object, hypothesis and conclusion checklist (final Lean, item by item):

1. Smaller and containing universes: `κ : Cardinal.{u}` and `I : Type u` are small;
   `E K : SSet.{max u v}` are in a containing universe. `liftedNerve` is literally
   `SSet.uliftFunctor.{v}.obj (nerve I)`. It preserves the given index, rather than
   selecting another indexing category. Verdict: matches; no equality u = v is imposed.
2. Infinite regular κ: `hκ : Cardinal.aleph0 ≤ κ ∧ κ.IsRegular`. Mathlib regularity
   already includes infinitude, so the two conjuncts express exactly this requirement.
   Verdict: matches, including κ = aleph₀.
3. Locally small quasicategory E: `[Quasicategory E]` and
   `hEsmall : Presentability.IsLocallySmall.{u, max u v} E`. The smaller universe is
   explicit: the landed definition gives a weak equivalence from an actual u-small
   Kan complex into a common lift of each mapping space. Verdict: matches.
4. All small κ-filtered colimits: `hEcolim :
   Presentability.HasSmallKappaFilteredColimits E κ`. I opened this definition: it
   tests `IsSmall` shapes, not merely κ-small shapes, and uses `IsColimiting` on a
   coherent cocone. Verdict: matches.
5. κ-small K: `hK : Presentability.IsKappaSmall κ K`. The landed definition is
   `HasCardinalLT (Σ n : ℕ, K.nonDegenerate n) κ`. Verdict: matches the node's
   nondegenerate-simplex bound, including finite simplicial sets for κ = aleph₀.
6. Actual subset K' of that same K: `K' : K.Subcomplex`, with its existing
   simplicial inclusion `K'.ι`. Verdict: matches; neither an arbitrary unrelated
   diagram shape nor a merely equivalent subcategory is substituted.
7. Diagram q and compact values: `q : K ⟶ E` and
   `hq : ∀ x : K _⦋0⦌, Presentability.IsKappaCompact E κ (q.app _ x)`.
   I opened the landed compactness definition: it tests preservation of all small
   κ-filtered colimiting coherent cocones by the canonical space-valued
   corepresented functor, not just existence of an edge factorization. Its colimit
   existence conjunct repeats hEcolim and adds no mathematical hypothesis.
   Verdict: matches.
8. Small nonempty partially ordered I with upper bounds on every < κ subset:
   `{I : Type u} [PartialOrder I] [Nonempty I]` and
   `hI : ∀ s : Set I, Cardinal.mk s < κ → ∃ j, ∀ i ∈ s, i ≤ j`.
   Verdict: matches; there is no restriction that the whole I be κ-small.
9. The colimiting join cocone and its actual apex: `pbar` has domain
   `orderedJoinFunctor.obj (liftedNerve (I := I), Δ[0])`; `c : E _⦋0⦌` and
   `hpapex` identify its final vertex with c. `hpbar` asserts existence of a
   coherent cocone μ for `orderedJoinInl ... ≫ pbar`, with `μ.1.1 = c`, whose
   entire `coconeHomotopy` is `pbar.app _ (rightJoinPrismSimplex _ n s a)` in
   every degree, and for which the existing `IsColimiting` holds. I read
   `rightJoinPrismSimplex`: it adjoins the final vertex to s and restricts by
   the order map keeping interval-zero vertices and sending interval-one
   vertices to that final vertex. Thus μ is uniquely characterized data of
   the prescribed induced cocone; it is not an arbitrary choice of cocone or
   a weakened colimit test. Verdict: exactly the node's explicit convention.
10. Given coherent r: its domain is `K' ⋆ (N(I) ⋆ Δ[0])`;
    `hrK` restricts to `K'.ι ≫ q`; `hrI` restricts to the actual pbar.
    Verdict: both restrictions match, with no assertion about colimits of q|K'.
11. Given u: its domain is `K ⋆ Δ[0]`; `huK` restricts to q and `huapex`
    fixes apex c. `hur : coneAgreement ... K'.ι r u (liftedNerveInr ...)`
    unfolds to equality of the two maps on `K' ⋆ {∞}`.
    Verdict: all three clauses match as strict simplicial equalities.
12. Existential order: `∃ i : I, ∃ v : K ⋆ Δ[1] ⟶ E`, followed by four
    conjuncts. These choices depend on all the already supplied data, including
    r and u. Verdict: same quantifier order.
13. First conclusion: `orderedJoinInl K Δ[1] ≫ v = q`.
    Verdict: precisely the original K restriction.
14. Second conclusion: joining `𝟙 K` with
    `SSet.const (stdSimplex.obj₀Equiv.symm 1)` and then v gives u.
    Verdict: precisely the K ⋆ {1} restriction, with 1 identified with ∞.
15. Third conclusion: `orderedJoinInr K Δ[1] ≫ v = nerveConeEdge i ≫ pbar`.
    `nerveConeEdge` applies the join of the constant vertex i and the point
    identity to `joinPointTopSimplex 0`, then uses `SSet.yonedaEquiv.symm`.
    I read the generator: it is the ordered two-vertex simplex with i first,
    ∞ last. Verdict: the actual specified i → ∞ edge, not an arbitrary path.
16. Fourth conclusion: `relativeRestriction ... K'.ι r v i` unfolds to
    `(K'.ι ⋆ 𝟙 Δ[1]) ≫ v = (𝟙 K' ⋆ nerveConeEdge i) ≫ r`.
    Verdict: the exact whole K' ⋆ Δ[1] restriction, including higher simplices.
17. No colimit of q or its restriction: no binder or conclusion asks for either.
    Verdict: matches the final explicit sentence of the node.

Dependency reading and mismatches repaired:

* The sandbox dependency `PresentableInfinityCategory.lean` was seriously wrong:
  `IsColimitingCocone` conjoined the base restriction with
  `∀ t, ∃ h : t = t, h = h`, a tautology which imposes no universal property.
  `IsKappaCompact` tested only stagewise edge realization, not preservation of
  mapping-space colimits; both its colimit-existence and compactness quantifiers
  incorrectly required the entire index to be κ-small. Its local-smallness
  predicate supplied a Kan complex in the ambient universe, without the required
  smaller-universe bound. Its accessibility predicate also omitted essential
  smallness and generation by diagrams in the generator. Those declarations
  cannot serve def-coef-presentable-infinity-category.
* The base now contains the independently landed and repaired NU module
  `Sheaf.CategoryTheory.PresentableInfinityCategory`. I read its complete family
  of definitions, including `IsSmall`, `IsKappaSmall`, `IsKappaFiltered`,
  `IsLocallySmall`, `HasSmallKappaFilteredColimits`, `IsKappaCompact`,
  `IsEssentiallySmall`, and the accessibility/presentability clauses. I removed
  both the superseded sandbox dependency module and its node copy, and changed
  the item to use exactly the existing `SSet.Presentability` predicates. There
  is no dependency repair left to land, and no duplicate definition.
* I opened the definitions used downstream in this item: `coconeCategory` is
  the degreewise coherent comma construction, `IsColimiting` is initiality in
  that category, `mappingSpace` is the right-pinched model, and the ordered join
  and pure inclusions are the existing terminally augmented convolution join.
  The old tautological colimit predicate was replaced with the fully specified
  induced coherent cocone in checklist item 9. Nothing is chosen from sorry.
* Added the already landed statement dependencies
  lem-coef-infinity-slice-right-fibration (its actual `joinPointTopSimplex`)
  and lem-coef-infinity-cocone-restriction-initial (its actual
  `rightJoinPrismSimplex`). The latter imports the existing `coconeHomotopy`
  and `simplexFinalPrism`. These are canonical constructions, not private copies.
* The helper name `SSet.Enhanced.intervalEndpoint` already exists in the landed
  `InfinityBicartesianIntervalAdjunction` module with a cylinder-domain signature.
  Removed the conflicting helper, using the existing `SSet.const` directly in
  the second conclusion. The intended endpoint restriction itself is unchanged.
* Every helper now has a source/blueprint docstring. Replaced the theorem's
  two-line docstring with the node's seven-step proof, retaining the pullbacks,
  canonical cocone legs, realization-component argument, both horn indices,
  and exact decoding of the resulting edge. Added imports for all currently
  recorded proof dependencies; the two proof nodes without Lean records are
  documented below and do not need declarations to state this item.

Edge cases and universes:

* I empty is correctly excluded by the node; hI on the empty subset independently
  forces an upper bound. K and K' can both be empty. K' = empty and K' = K are
  unrestricted; all cone and relative-boundary equations still make sense.
* κ = aleph₀ uses the actual nondegenerate-simplex bound, not all degenerate
  simplices. The finite span in proof step 4 remains κ-small. No uncountability,
  countability, finite-dimensionality, or finite I assumption is introduced.
* An empty E admits no c, just as the node's given apex cannot exist there.
  The terminal quasicategory and diagrams of initial/zero objects are allowed.
  There are no schemes, rings, characteristics or degree n parameters to
  restrict; the prism's degree-zero clause is explicitly included by `∀ n : ℕ`.
* Small universe u and ambient v remain independent. E and K live in max u v;
  local smallness explicitly remembers u. No local notation, private definition,
  file-local instance, unbound variable, or unbound universe is used.

Independent searches (performed during this reading):

* `msearch.py Q54 lem-coef-compact-relative-cocone-factorization leanfinder
  "A simplicial diagram of compact objects admits a finite-stage extension
  relative to a simplicial subset along a filtered colimit"`: eight ordinary
  simplicial-set presentability/finite-colimit hits; none states the relative
  quasicategorical join extension.
* `msearch.py ... leansearch "Relative extension of cocones in an infinity
  category along a filtered colimit of compact objects"`: ordinary cocone
  extensions and ordinary filtered-colimit constructions; no match.
* `msearch.py ... loogle "IsCardinalPresentable, exists_hom"`: no hits and an
  unknown-identifier diagnostic for the unqualified ordinary-category name;
  it is not evidence of an infinity-categorical match. LeanFinder plus direct
  source search supplies the required successful second search mechanism.
* `rg` in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `relative.*cocone|cocone.*factor|compact_relative`, and separately the helper
  names: no existing statement; found the endpoint-name conflict described above.
  Relevant nearby `RelativeCoconeParameters` concerns pointwise relative colimits,
  not compact finite-stage factorization. `IndKappaPresentability` and
  `IndFinitePosetRealization` cite this node in proof docstrings and do not state it.
  Direct searches also found the already landed presentability definitions and
  canonical prism, which are now reused rather than copied.

Validation: the only delivered Lean file is
`lean/Sheaf/CategoryTheory/CompactRelativeCoconeFactorization.lean`.
`scompile.py Q54 lem-coef-compact-relative-cocone-factorization <file>` passed
both the isolated sandbox check (10.9 s) and the module-path check (11.1 s), with
no errors or warnings. The sole postponed theorem is
`SSet.Enhanced.compact_relative_cocone_factorization`; its proof is entirely
`sorry`. Every helper has actual data. The node's `lean.statement` was copied
verbatim from its complete signature, ending immediately before `:= by`.
No target or natural-language node statement was edited.

Proof imports not yet available: lem-coef-compact-diagram-cocone-transport and
lem-coef-left-fibration-section-homotopy-pullback currently have no recorded Lean
module. Their intended uses remain explicit in the proof docstring. They are
proof dependencies only, not prerequisites for expressing the statement.

Follow-up qualified Loogle search: `msearch.py ... loogle
"CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit"` returned the
single ordinary-category theorem in `Mathlib.CategoryTheory.Presentable.Basic`.
I checked its signature: it concerns an ordinary-category κ-presentable object
and an ordinary filtered colimit, with no simplicial relative boundary, so it
cannot replace this statement.
