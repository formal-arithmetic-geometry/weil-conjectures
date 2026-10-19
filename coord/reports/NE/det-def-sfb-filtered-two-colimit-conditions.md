## Worker report

Stage-1 worker report: det-def-sfb-filtered-two-colimit-conditions

## Files written

- `dag/nodes/sec-six-functors-basics/det-def-sfb-filtered-two-colimit-conditions.json`: imported definition checked and marked `split`; statement preserved; no new nodes and no Mathlib leaves.
- `citations.json`: empty, because a definition has no proof steps.
- `report.md`: this report.

## Attachments

No module was written. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`, the shared `lean/WeilConjectures/`, Mathlib, and `lean/Sheaf` by the exact blueprint tag, by `filtered two colimit`, and by `CategoryCocone`, `IsFilteredTwoColimit`, `EssSurjObj`, `HomSurj`, and `HomInj`. The shared project contains the exact declaration `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` in `WeilConjectures/CategoryTheory/FilteredTwoColimit.lean`; therefore the existing declaration is attached below and no duplicate module is written.

## WANTED

None.

## Corrections and scope

The statement is unchanged. I read the chapter record `dag/chapters/sec-six-functors.json`, the current blueprint section `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-filtered-two-colimit/_section.md`, the exact blueprint node and its source text, and the existing dependency `det-def-sfb-filtered-two-colimit-cocone`. The dependency already introduces a preordered index, categories, transition functors, vertex category, comparison functors, and natural isomorphisms, so the item’s three clauses are well-typed and its `stmt_deps` is complete. The imported `unreachable` flag was preserved.

The item is a definition, so splitting it means recording the defining predicate and its existing cocone dependency; adding separate nodes for Obj, Hom-surj, or Hom-inj would be clause restatements forbidden by the stage-1 contract. The explanatory final paragraph is part of the definition’s prose and introduces no additional theorem. The parent `sk-def-sfb-filtered-two-colimit` records the same predicate; the existing DAG metadata is preserved by delivery. No source error or statement dispute was found, and no SGA source is involved.

## Mathlib searches

All four required searches were run with `msearch.py NE det-def-sfb-filtered-two-colimit-conditions`; their exact queries and actual result summaries are recorded in the node’s `mathlib_searches` and in the authentic `searches.jsonl` log. LeanSearch and LeanFinder returned only filtered colimit/type or general cocone results; Loogle reported the expected project identifier as unknown; grep found unrelated RingTheory occurrences and no Mathlib two-colimit predicate. The exact project declaration is recorded as the existing Lean realization, so this definition is not duplicated.

## Not duplicates

No new node was created, so there are no duplicate pairs. The existing `det-def-sfb-filtered-two-colimit-cocone` node is the statement dependency and is a different definition: it supplies the cocone data, while this item supplies the three filtered 2-colimit conditions.

## Review by NE

I checked each clause against the current blueprint node and section source. `(Obj)` quantifies an arbitrary vertex object `d` and supplies a stage, stage object, and isomorphism. `(Hom-surj)` quantifies arbitrary stages, objects, and a vertex morphism, then supplies a common upper stage and a transition-stage morphism; the composite is typed because the inverse of `theta_{ik,x}` goes from `Phi_i(x)` to `Phi_k(T_{ik}x)` and `theta_{jk,y}` goes from `Phi_k(T_{jk}y)` to `Phi_j(y)`. `(Hom-inj)` quantifies two stage morphisms with equal images and supplies a later stage where their transition images agree. These are exactly the three defining clauses, with no directedness, coherence, identity, or composition hypothesis added.

I opened the statement of `det-def-sfb-filtered-two-colimit-cocone` and verified that it defines every symbol used by the item, including the orientation and components of `theta`. I checked small edge cases conceptually: an empty index or vertex category makes the universal clauses behave as written; a one-stage cocone with identity transition and structure isomorphism reduces Hom-surj to ordinary fullness and Hom-inj to faithfulness of that stage functor. No hidden fact beyond the cited cocone definition is used. Since the item has no proof steps, `citations.json` is correctly empty. The split has no new definitions, statements, or Mathlib leaves and has no dependency cycle.

## Unfinished work

No new Lean module is needed: the existing declaration is attached. The prescribed delivery wrapper checks its imported type in the current compile environment. No live Lean source was modified.

## Second reading by NE

- Node statement: I read the source `det-def-sfb-filtered-two-colimit-conditions.md` and matched its sole dependency to `det-def-sfb-filtered-two-colimit-cocone`. The Lean declaration `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` in `WeilConjectures.CategoryTheory.FilteredTwoColimit` is a `Prop` structure with fields `essSurjObj`, `homSurj`, and `homInj`. The former renders (Obj): `∀ d, ∃ i x, Nonempty ((c.Φ i).obj x ≅ d)`, equivalent to the source's displayed `d ≅ Φ_i(x)` by inversion. The latter two render exactly the quantified Hom-surj and Hom-inj clauses, including the witnesses `k`, `hi : i ≤ k`, `hj : j ≤ k`, `g`, and `k'`, `h : k ≤ k'`, with the displayed composition and equalities. Verdict: exact statement.
- Data and hypotheses: `CategoryCocone` supplies a preorder `I`, categories `C i` and `D`, transition functors `T`, vertex functors `Φ`, and isomorphisms `iso : T h ⋙ Φ j ≅ Φ i`; its signature supplies no directedness, identity, normalization, coherence, finiteness, or universe equality. Verdict: no hypothesis added or omitted.
- Conclusion and explanatory content: the structure has precisely the three Prop fields and no stronger comparison-category or equivalence assertion. The source's final paragraph is explanatory prose and introduces no fourth clause. Verdict: no clause strengthened or weakened.
- Edge cases: an empty `I` leaves Hom-surj and Hom-inj vacuous and makes Obj impose the corresponding emptiness of `D`; an empty `D` is handled by the same quantifiers. With one index and identity data, the clauses specialize to essential surjectivity, fullness, and faithfulness. Non-directed preorders remain allowed because no `IsDirected` instance occurs. Zero or empty categories and all allowed universe levels are covered by the polymorphic upstream signature.
- Existing-definition search: I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` for `CategoryCocone`, `IsFilteredTwoColimit`, `EssSurjObj`, `HomSurj`, and `HomInj`, and read the exact upstream declaration at lines 63–100. The declaration is the unique exact project match; no new module or duplicate definition is needed. The node's Lean record now points to this existing declaration, and no source file was written.
- Independent semantic search: `msearch.py NE det-def-sfb-filtered-two-colimit-conditions leanfinder "joint essential surjectivity with eventual lifting and equality of arrows in categories over a preorder"` returned eight Mathlib candidates, including `CategoryTheory.Functor.IsLocallyDirected.cond`, `CategoryTheory.Comma.essSurj_map`, and `SmallObject.SuccStruct.Iteration.subsingleton.MapEq`. I read `CategoryTheory/LocallyDirected.lean`: its `cond` is an element-lifting condition on a single Type-valued functor, not these three clauses on varying source categories. `Functor/ReflectsIso/Jointly.lean` defines immediate joint faithfulness for a common source, also different. A separate `rg` search for `bicolimit|2.colimit|TwoColimit|eventual.*equal|JointlyFaithful` in Mathlib, the old slopmaster2 tree, and `lean/Sheaf` found no alternative exact predicate; `PointFdQbarCategory` imports the same upstream definition for a special application.
- Source confirmation: `scompile.py --source WeilConjectures.CategoryTheory.FilteredTwoColimit` returned the current source, whose declarations at lines 57–100 agree with the shared copy read above. The module prose's discussion of directed coherent comparison categories is not an extra Lean hypothesis: the actual binders are `{I : Type w} [Preorder I] (C : I → Type u) [∀ i, Category.{v} (C i)] (D : Type u') [Category.{v'} D]`, and the predicate has argument `c : CategoryCocone C D`. All five universes are independent; no variable is unbound.
- Hom-surj arrow-by-arrow check: `(c.iso hi).inv.app x` goes from `Φ_i x` to `Φ_k (T_ik x)`; `(c.Φ k).map g` goes to `Φ_k (T_jk y)`; `(c.iso hj).hom.app y` ends at `Φ_j y`. Lean's `≫` is left-to-right composition, so `f = (c.iso hi).inv.app x ≫ (c.Φ k).map g ≫ (c.iso hj).hom.app y` is exactly the source's formula. Hom-inj is `∀ (k : I) (x y : C k) (g g' : x ⟶ y), (c.Φ k).map g = (c.Φ k).map g' → ∃ (k' : I) (h : k ≤ k'), (c.T h).map g = (c.T h).map g'`, with the same quantifier order and no extra constraint on `k'`.
- Definitions and proofs: all four existing predicates/structures have concrete data/formulas and contain no `sorry`; no theorem was proved or added. This definition node has no proof steps. There are no new definition nodes, dependency modules, or statement corrections to audit. The zero object, characteristic, scheme, and degree cases add no further conditions to this category-only definition.
- Signature check: `lean.statement` is exactly `structure IsFilteredTwoColimit : Prop`, the source signature from `structure` up to `where`.
- Changes: repaired the missing `lean` record by attaching `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` (`structure IsFilteredTwoColimit : Prop`) and documented why its three fields render the node verbatim. No mathematical statement, dependency, or source text changed.

Validation: `deliver2.py NE det-def-sfb-filtered-two-colimit-conditions --no-push` printed `OK (dry run): commit b04adec8a8 passes the preflight and compiles; nothing pushed`. The wrapper checked the existing declaration with an imported `#check` in the current compilation environment. The final node copy also records the complete source signature `structure IsFilteredTwoColimit : Prop`. No new Lean files require compilation.
