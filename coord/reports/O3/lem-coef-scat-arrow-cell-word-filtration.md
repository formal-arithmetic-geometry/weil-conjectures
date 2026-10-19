## Worker report

The module `Sheaf.CategoryTheory.ArrowCellWordFiltration` defines the two-object simplicial
category `arrowCellTwo K`, its induced map `arrowCellTwoMap`, tensor powers of simplicial sets,
the old-arrow factors `arrowCellH`, the alternating summands `arrowCellM`, and their coproduct.
`ArrowCellPushout` records the pushout cocone and its universal property. `ArrowCellReduction`
and `ArrowCellWordQuotient` record the degreewise reduction equivalence and quotient map.
`ArrowCellWordFiltration` states the remaining clauses: the pushout object set is the old object
set; every mapping simplicial set is the alternating-word quotient; `filtration w z k` starts at
`hom C w z`, has monomorphic transitions, is exhausted by the colimit, and has the displayed
attaching pushout for every positive stage; the naturality field gives compatible maps for every
enriched functor, and the inclusion is bijective on objects and monic on mapping simplicial sets.
The theorem `CategoryTheory.CoherentNerve.arrow_cell_word_filtration` has exactly the node's
hypotheses: degreewise injective `i : K ⟶ L`, a small simplicial category `C`, and an enriched
functor `h : U(K) ⟶ C`; its proof is `sorry` as required for stage 2.

The node's hypotheses render as follows:

* “small simplicial sets” are `K L : SSet.{u}` and “degreewise injective” is
  `hi : ∀ n, Function.Injective (i.app n)`.
* “small simplicial category” is `C : SCat.{u}` from
  `CategoryTheory.CoherentNerve.SCat`.
* “the two-object category `U(K)` and attaching functor” are `arrowCellTwo K` and
  `h : arrowCellTwo K ⟶ C`; its selected objects are `h.obj (ULift.up Bool.false)` and
  `h.obj (ULift.up Bool.true)`.
* `H_k` is `arrowCellH C x y w z k`, and `M_k` is `arrowCellM C L x y w z k`; its
  coproduct is `arrowCellWordCoproduct`.
* The quotient relation is the degreewise `ArrowCellReduction.relation`, required to be an
  equivalence, and `ArrowCellWordQuotient.degreewiseQuotient` makes the quotient map
  surjective in each simplicial degree.
* `P_0 = C(w,z)` is `filtration_zero`; monomorphic transitions are `filtration_mono`; the
  sequential colimit is `filtration_colimit` and `mappingQuotient` identifies it with the
  pushout mapping simplicial set.
* The positive-stage boundary is represented by `Q`, `qL`, the coordinate witness that some
  coordinate comes from `K`, and `qM`, `r`, `b` with
  `IsPushout qM r b (stageTransition w z k)`.
* Naturality is the `naturality` field, which quantifies every enriched `F : C ⟶ D` and gives
  transition-compatible maps; `inclusion_identity` and `inclusion_mapping_mono` state the final
  inclusion clauses.

Dependencies used: `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`, specifically
`SSet.Bergner.U`, `SSet.Bergner.bundle`, `SSet.Bergner.uMap`, `SSet.Bergner.bundleMap`, and the
landed `CategoryTheory.CoherentNerve.SCat`/`sCatCategory`; and Mathlib's
`CategoryTheory.Limits.colimit`, `CategoryTheory.Limits.PushoutCocone`, `CategoryTheory.IsPushout`,
`CategoryTheory.Mono`, `CategoryTheory.EnrichedCategory.comp`, and the simplicial-set monoidal
product. The node dependency `def-weil-pbc-category-colimit` is represented by Mathlib's chosen
`colimit` and its universal cocone.

Edge cases checked against the statement and the source calculation: `k = 0` uses only `M_0`
and the filtration base, while the attaching square is required only for `k ≥ 1`; `k = 1` has
no intermediate old-arrow tensor factor; `K = ∅` gives no reductions; `K = L` reduces every
positive new-arrow coordinate; `L = ∅` leaves no positive words; repeated endpoints `x = y`,
empty old mapping simplicial sets, multiple `K` coordinates, identity old arrows, and enriched
functors identifying objects are all allowed by the binders and fields. No complement of `K` is
asserted to be simplicial.

Searches made: `msearch.py leanfinder` for “mapping simplicial sets after freely adjoining an
enriched arrow have a word length filtration”; `msearch.py loogle` for
`CategoryTheory.SimplicialCategory, CategoryTheory.Limits.pushout`; `msearch.py leansearch` for
“mapping spaces in a pushout of enriched categories adjoining morphisms are filtered by words”;
`msearch.py grep` for `Bergner|Dwyer.?Kan|word.?length|enriched.*pushout` under Mathlib's
`CategoryTheory`; `rg` over `lean/Sheaf` and the read-only `WeilConjectures/` checkout for
`arrow-cell`, `word-filtration`, and free simplicial-category pushouts. These found no existing
declaration of this construction. The existing `CategoryTheory.CoherentNerve.SCat` and landed
`simplicial_interval_lifting` were used rather than redefined.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Earlier second reading (a previous round; superseded)

I reread the node, the full dependency records, the landed interval-lifting module, and the new
module. The theorem binders match the node's `K ↪ L`, `C`, and `h : U(K) ⟶ C`; repeated endpoint
objects remain permitted. The module renders the displayed `H_k` and `M_k` products, records the
reduction quotient in every degree, starts the filtration at `hom C w z`, states monomorphic
successor maps and the sequential colimit, and includes the positive-stage boundary condition
and pushout square. The naturality binder quantifies arbitrary enriched functors and does not add
faithfulness or object-injectivity. The inclusion fields retain bijectivity on objects and
mappingwise monomorphisms. The cases `k=0`, `k=1`, empty `K` or `L`, `x=y`, and object-identifying
functors were checked directly in the definitions. The source and blueprint identifiers occur in
every module and declaration docstring, and the only postponed proof is the node theorem.

## Second reading by N3

I independently opened the item, both statement-dependency records and their declarations,
the module, and the source. The source is **HTT**, not a Stacks tag: I read the online PDF,
Appendix A.3.2, the standing conventions on printed pp.856–858 and the full word calculation
in the proof of Proposition A.3.2.4, printed pp.859–860 (PDF pages 876–877).
The calculation specializes to simplicial sets with their cartesian product; it assumes no
Kan condition on the mapping sets, distinctness of the selected objects, or injectivity of
an auxiliary functor's object map. No extra hypothesis from the general model-category
proposition is needed for this explicit simplicial-set construction.

The worker report and the earlier reading above describe the initial file. Contrary to that
reading's verdict, the initial file had substantial H3 defects. The following is the review
of the repaired delivery. The natural-language node is unchanged, so no `statement_change`
or citer audit is appropriate.

The statement inventory and its Lean rendering, checked item by item:

1. **Small simplicial sets and degreewise inclusion.** `K L : SSet.{u}`, `i : K ⟶ L`,
   and `hi : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (i.app n)` retain exactly the
   hypotheses. There is no cofibrancy, fibrancy, cardinality or nonemptiness assumption.
   Verdict: matches.
2. **Small simplicial category with arbitrary-object enriched functors.** `C : SCat.{u}`
   is the landed `CategoryTheory.CoherentNerve.SCat`, whose definition and `sCatCategory`
   instance I opened in `CoherentNerveInfrastructure.lean`. Its arrows really are
   `EnrichedFunctor SSet C D`, with unrestricted object functions. `h : arrowCellTwo K ⟶ C`
   selects `h.obj ⟨false⟩` and `h.obj ⟨true⟩` and the forward mapping-set map.
   I read `Fixed`, `FixedHom`, `bundle`, `bundleMap`, `U`, `uHom`, `uMap` in the recorded
   `SimplicialIntervalLifting.lean`: the forward mapping set is exactly `K`, the endomorphism
   sets are terminal, and the reverse mapping set is empty. `arrowCellTwo` and
   `arrowCellTwoMap` only bundle these dependency constructions. Verdict: matches.
3. **Pushout and literally unchanged objects.** `ArrowCellPushout.enrichment` is a genuine
   `Fixed C`, wrapped in `ULift.{0}` solely to prevent Lean from treating the new enrichment
   as the local instance on the old category. Its bundle has object type literally `C`.
   `old : FixedHom (EnrichedCat.str C) enrichment.down` has object map the identity;
   `inL`, `comm`, and `universal : IsColimit (PushoutCocone.mk ...)` are the actual pushout
   cocone in `SCat`. `newArrow_eq` identifies the distinguished new-arrow map with the
   actual `inL` mapping map. This replaces an unrelated equality of carrier types and a
   merely bijective old object function. I also read the colimit dependency's Mathlib
   `colimit`, `Cocone`, `IsColimit` signatures in `Limits/HasLimits.lean` and the pushout
   cocone interface. Verdict: exactly the stated universal-property meaning.
4. **H_k, M_k and alternating labels.** The correct existing definitions `sSetTensorPower`,
   `arrowCellH`, `arrowCellM`, and `arrowCellWordCoproduct` are retained. `M_0` is literally
   `hom C w z`; for positive `k`, `H_k` is the stated product and `M_k = H_k × L^k`.
   The tensor is the cartesian simplicial product, verified in Mathlib's simplicial-set
   monoidal implementation. `ArrowCellWord.ofOld` and `.snoc` encode exactly these typed
   words, with endpoints on every old label. `arrowCellPositiveWord` and `arrowCellWordOfM`
   decode the actual product coordinates into their alternating order. Each word of length
   `k` corresponds to its `M_k` tuple, with only terminal factors suppressed.
   Verdict: matches all labels and endpoints, including equal selected objects.
5. **Specified quotient, natural simplicial presentation, and composition.**
   `ArrowCellReduction.last` deletes a genuine coordinate `i.app n t`, using the actual
   `h.map` and actual enriched composition; `.earlier` permits that deletion at every
   position. There are no other generators. `quotient_kernel` is an **iff** between equal
   evaluated words and `Relation.EqvGen (ArrowCellReduction i h n)`.
   `quotient_surjective` covers every mapping simplex. `ArrowCellPushout.evaluate` is a
   real recursive evaluation using the two pushout legs, not an arbitrary function.
   `wordMap_evaluation` and `quotient_summand` identify the simplicial coproduct map with
   this evaluation on every tuple. Thus the surjection and exact kernel describe the
   simplicial quotient by precisely the specified relations, with coordinatewise simplicial
   operators inherited from the actual `M_k`; they give its natural isomorphism with the
   pushout mapping set, rather than merely an unrelated surjective map.
   `ArrowCellWord.concat` explicitly merges the old arrows at the join;
   `composition` identifies its evaluation with pushout composition. Verdict: matches.
6. **Actual length filtration and its base.** `stages w z : ℕ ⥤ SSet` uses the preorder
   category on the natural numbers. `stage_image` is an **iff** identifying the range of
   the monic `inclusion w z k` with evaluated words of length at most `k`.
   `zeroIso` and `zero_inclusion` identify stage zero with the original mapping set through
   its actual old-leg map. `transition_mono` applies to the functor's actual successor map,
   with no unrelated second family of transitions. Verdict: exactly `P_k` and `P_0`.
7. **Sequential colimit.** `inclusion_natural` makes those stage inclusions a cocone with
   vertex the pushout mapping simplicial set. `colimit` asserts `IsColimit` of that very
   cocone over `ℕ`, with the same transition maps. The initial discrete coproduct, with
   the wrong vertex, was removed. Verdict: the stated sequential universal property.
8. **Full boundary and canonical attaching square.** For stage `k+1`, `boundary k` is a
   subcomplex of the actual `L^(k+1)`. `boundary_obj` is an **iff** saying that one of the
   actual coordinates listed by `sSetTensorPowerLabels` is in the image of `K`.
   The top-left object is literally `(⊤ : H_(k+1).Subcomplex).prod (boundary k)`, so it is
   precisely `H_(k+1) × Q_(k+1)`; its top map is its subcomplex inclusion into `M_(k+1)`.
   `reduction_evaluation` fixes the left map by its value in the quotient. The quotient's
   exact reduction kernel and monic stage inclusion make this the class of any stated
   reduction, independently of which K-coordinate is chosen. `attaching` is `IsPushout`
   with this top map, this reduction map, the evaluated word map, and the actual successor
   transition. Verdict: all four objects and four arrows match, for every positive stage.
9. **Naturality under every F, including object identifications.** The theorem gives one
   family of presentations indexed by `C,h`, and for every `F : C ⟶ D` gives
   `ArrowCellNaturality F (P C h) (P D (h ≫ F))`. This packages the same universally
   quantified construction while ensuring the target is the presentation for `Fh`.
   `plusFunctor_old` and `plusFunctor_new` characterize the canonical induced functor by
   both pushout legs; `plusFunctor_obj` is `F.obj`, and `onHom_eq` gives its actual mapping
   maps. `word_natural` changes all old labels by `F` and leaves new labels unchanged.
   `stageMap` is a natural transformation of the sequential diagrams;
   `inclusion_natural`, `summandMap_word`, `wordMap_natural`, `boundary_natural`, and
   `reduction_natural` make the quotient, inclusions and all attaching-square arrows
   commute. The boundary map is a restriction of the actual summand map.
   Identity and composite maps are forced to be the canonical ones: evaluation is
   surjective, stage inclusions are monic, and the pushout factorization is unique.
   The initial quantification over arbitrary unrelated target filtrations was removed.
   Verdict: matches, without faithfulness or object-injectivity hypotheses.
10. **Final old inclusion.** `bundleMap pushout.old` is literally identity on objects;
    `inclusion_mapping_mono` is `Mono (pushout.old.map w z)` for every pair.
    Verdict: both final clauses, with the correct map.

Edge cases checked in the definitions and fields:

- `k=0` uses only `.ofOld`, `M_0`, and `zeroIso`; attachment squares are indexed by `k+1`.
  At `k=1`, the intermediate old-arrow tensor power is the terminal zeroth power.
- Empty `K` gives no generating reductions and empty positive boundaries. If `K=L` and
  `i` is the identity, every positive word reduces and each full boundary is all of `M_k`.
  Empty `L` leaves only length-zero words. No simplicial complement is used.
- The selected objects may coincide. Typed recursive words, reduction and concatenation
  remain valid, including loops, identity old arrows and multiple reducible coordinates.
- Empty old off-diagonal mapping sets are permitted. An empty `C` admits no `h`; no
  `Nonempty C` or dummy object is inserted. There is no ring, characteristic, zero object
  or scheme hypothesis in this node.
- Arbitrary degree `n : SimplexCategoryᵒᵖ` includes degree zero and every simplicial
  operator. A single explicit universe `u` covers small simplicial sets/categories at any
  size; there are no unbound universes or implicit variables. `ULift.{0}` adds none.

Independent searches (using different search phrases from the worker):

- `msearch.py ... leanfinder "Free enriched category adjoining an arrow pushout word normal
  forms and length filtration"`: only simplex-category generator/normal-form declarations;
  no arrow-attachment construction.
- `msearch.py ... loogle "Relation.EqvGen"`: exact Mathlib equivalence-closure definition,
  reused here; I opened `Logic/Relation.lean` and also checked the Church–Rosser dependency's
  recorded `Relation.church_rosser` / `equivalence_join_reflTransGen` signatures.
- `msearch.py ... leansearch "pushout of simplicial categories by adjoining a morphism
  described as words with relations"`: generic `IsPushout` and pushouts of types, not this
  enriched construction.
- `msearch.py ... grep "alternating.*word|word.*filtration|ArrowCellWord"`: Coxeter words,
  unrelated to this notion. Direct `rg` on the project's `lean/Sheaf`, read-only upstream
  `WeilConjectures`, and Mathlib's category/enriched/simplicial-set sources found no exact
  existing statement or construction. I opened `FreeFactorCategoryNormalForm.lean`:
  its words alternate arrows of two fixed-object ordinary categories with identity and
  factor-composition reductions; they do not represent a relative arrow attachment by an
  arbitrary simplicial map `K → L`, so neither that word type nor its theorem is a match.
  The dg cell calculus uses complexes and differential relations, also a different notion.
  I also searched monoidal/simplicial-set sources for tensor-power definitions: no existing
  finite cartesian-power construction matching the helper was found.

Repairs made: replaced the unconstrained equivalence relation and unconnected surjection;
added the actual reductions, exact quotient kernel, canonical evaluation and composition;
made the old object function literally identity; tied stages to bounded-length images;
replaced the discrete coproduct by the actual sequential colimit; replaced the arbitrary
attaching domain and arbitrary coordinate function by the full `H_k × Q_k` subcomplex;
fixed the reduction/word/successor maps; and replaced the impossible arbitrary-filtration
naturality assertion by canonical comparisons of the actual pushout presentations.
The correct product definitions and bundled dependency constructions were retained.
Expanded the theorem docstring to all eight proof steps of the node. Added the explicit
Mathlib relation import and synchronized `lean.statement` and `lean.declarations`.

No new DAG notion or dependency module was required: these helpers express constructions
already introduced by this node. Every definition has real data; the sole `sorry` is the
node theorem, whose docstring contains its complete proof plan and source/blueprint tag.
Every named declaration has the source and blueprint docstring. No private or local
notation/instance, no hidden `let`/`show` statement binder, no extra theorem, and no proof
beyond the stage-2 `sorry` was introduced. The final complete module compiles cleanly via
`scompile.py N3 lem-coef-scat-arrow-cell-word-filtration <absolute module path>` in both
its sandbox and module-name checks (3.7 s / 4.8 s), with no errors or warnings.
