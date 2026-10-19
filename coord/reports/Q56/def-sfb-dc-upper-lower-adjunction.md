## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-dc-upper-lower-adjunction.json`: existing definition, Mathlib leaf, matched by `CategoryTheory.Adjunction.restrictFullyFaithful` at `Mathlib/CategoryTheory/Adjunction/Restrict.lean:42`; its defining Hom equivalence is at lines 44–50 and its explicit formula at line 76. The statement is unchanged.
- `citations.json`: `[]`, since the leaf has no proof steps.
- `report.md`: this worker report and self-review.
- `searches.jsonl`: retained the earlier attempt's actual search log and appended four searches executed in this pass.

There are **0 new nodes and 1 Mathlib leaf** (the item itself).

## Attachments

None. Searches in the complete read-only slopmaster2 `WeilConjectures/` and `Comparator/` trees for the exact blueprint id/tag and `boundedConstructibleUpperStarLowerStarAdjunction` returned no matches. A concept search found `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.leftDerivedUpperStarAdjunction`, `WeilConjectures/SixFunctors/Etale/Derived/Adjunctions.lean:135`; I read its assumptions and type. It is for finite ordinary ring coefficients on the étale site, with invertible exponent, whereas this item is for module objects over a pulled-back commutative condensed ring on the pro-étale site. It does not state this item.

The master reference `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:178–185` uses the same generic Mathlib restriction, but its restricted functors depend on sorried preservation lemmas. Master is reference material only, so this is not an attachment.

## WANTED

None. All sources needed for the item and the generic restriction construction are available locally.

## What was wrong or changed

The existing sandbox already had a correct Mathlib-leaf candidate. I retained its unchanged statement, four statement dependencies, empty proof, empty proof dependencies, null proof origin, blueprint identity and empty `same_as`. The imported source's one proof paragraph uses the ambient derived adjunction, the restricted functors' compatibility with inclusions, and the full-subcategory Hom identification. These are explicitly supplied by `def-sfb-module-derived-pushpull-adjunction`, `def-sfb-dc-upper-star`, `def-sfb-dc-lower-star`, and `def-sfb-bounded-constructible-complexes`. They are data for the Mathlib construction, not replaced by an unsupported preservation argument.

I added fresh Mathlib searches and made `mathlib_match.how` spell out the categories, inclusions, comparison directions and source lines. I rewrote the historical report: the earlier second-reading text asserted delivery authorization and referred to previous dry runs; this worker's handoff is the required no-push dry run for a fresh second reader. No claim of a new independent second reader is made here.

The shared snapshot has no chapter/unit JSON records for this newly imported section (search of `dag/chapters/` and `dag/units/` for its identifiers returned none). I read the current blueprint chapter and unit `_section.md` files and the unit's proof directly. No chapter, unit, maintainer metadata, or source statement was edited.

## Not duplicates

No new nodes. Whole-DAG searches for `restrictFullyFaithful`, ambient-adjunction restriction and the exact Hom-bijection wording were supplemented by whole-blueprint `blueprint_refs.py search` queries `adjunction restriction`, `upper-lower-adjunction` and `Hom-bijections`. The last query finds only this item. The containing restricted-functors unit packages several distinct functors and their structure; the ambient adjunction node is on the larger derived categories; the coextension adjunction concerns a ring-object morphism. None requires a duplicate child for this item. `blueprint.from` remains null because this is an imported blueprint node; its exact proof paragraph is recorded in `split_report.blueprint`.

## What could not be finished

Nothing remains for this stage-1 item. Preservation and construction of the ambient adjunction remain obligations of the existing dependency nodes. The Mathlib-leaf designation here identifies the generic restriction construction; it does not assert that all its statement dependencies are already finished.

## Review by Q56

I read main-20261015 `sec-six-functors-basics/_section.md`, the restricted-functors unit `_section.md` and `sk-def-sfb-dc-restricted-functors.proof.md`, and the item's statement and `.proof.md`. The chapter separates fixed abelian coefficients from condensed ring module objects; this item is in the latter layer. The unit's route is to restrict existing ambient functors and their adjunctions along full inclusions. The Mathlib construction follows that route exactly, without a new derived-functor construction. There is no SGA citation.

I opened the statements of all four dependencies and their blueprint sources. `def-sfb-dc-upper-star` explicitly defines the restricted ambient pullback and says it commutes with inclusions. `def-sfb-dc-lower-star` explicitly assumes preservation of bounded constructible complexes by the ambient pushforward, then defines the restricted pushforward and says it commutes with inclusions. Thus the item retains the preservation hypothesis and does not claim it for every condensed ring. The setting inherited through lower-star is separated schemes of finite type over a field of characteristic p > 0, with a fixed prime ell different from p. No properness, smoothness or further coefficient condition is introduced. `def-sfb-module-derived-pushpull-adjunction` states the ambient total-derived adjunction itself, not just a definition of either functor. `def-sfb-bounded-constructible-complexes` explicitly states that the constructible category is the full subcategory of the ambient module-object derived category. This is precisely the Hom identification required, with no appeal to a dependency's proof instead of its statement (C3/C4).

For the original source's single proof paragraph, its first assertion (the ambient Hom bijection) is provided by the ambient-adjunction statement; its second assertion (the same Hom-sets after restriction) is provided by the two restricted-functor definitions and the full-subcategory definition. To check the concluding naturality assertion and the actual bijection, I read `Mathlib/CategoryTheory/Adjunction/Restrict.lean:26–59,76–85`. Set C = D_cons(Y,Lambda), D = D_cons(X,Lambda), C' and D' equal to the respective ambient module-object derived categories, and iC and iD equal to their full inclusions. Set L', R' to the ambient derived functors and L, R to their restrictions. The comparison comm1 has direction iC followed by L' to L followed by iD, and comm2 has direction iD followed by R' to R followed by iC; invert the master compatibility isomorphisms to match these directions. These comparisons are canonical identities on underlying objects and morphisms for full-subcategory restrictions. The defining equivalence first applies hiD.homEquiv, identifies the left functor by comm1, applies the ambient adj.homEquiv, identifies the right functor by comm2, and applies hiC.homEquiv.symm. Hence it is exactly the ambient Hom bijection under the canonical identifications, including the item's final clause. Naturality is proved in lines 52–59; the formula at line 76 confirms this is the specified adjunction, not merely some adjunction with the same two functors. This is one application of the generic Mathlib definition, satisfying B6/B8. The delivered leaf consequently has no proof steps or step citations; `citations.json = []` is complete. No extra categorical theorem is hidden in a step (C1/C2).

The fresh wrapper searches were: LeanFinder on `An ambient adjunction restricts to full subcategories when both functors preserve the subcategories, with the ambient Hom equivalences`; Loogle on `"restrictFullyFaithful"`; directory grep on `^noncomputable def restrictFullyFaithful|^lemma restrictFullyFaithful_homEquiv_apply` in `CategoryTheory/Adjunction`; LeanSearch on `Restrict an adjunction to full subcategories with the same Hom bijections`. All four succeeded; the semantic searches returned the restriction construction and its Hom formula, and grep returned actual declaration lines 42 and 76. I read the source before recording the match. Earlier unsuccessful or unavailable queries are retained with their accurate original outcomes; no unsuccessful search is used to infer absence. The earlier successful alternative phrasings are also retained and backed by `searches.jsonl`. No search was invented.

For B1–B5/B7/B9/B10 and D1–D5, there are no new nodes to hide an elementary step, restate a clause or leave partly split. All referenced ids exist and are unmerged. The item is self-contained through its explicit definition dependencies; its TeX and statement are unchanged. It retains imported blueprint fields and flags, and `same_as` records the search. No exact project attachment was found; finite étale coefficients were not silently identified with condensed module coefficients.

For E1–E7, I checked the source and target of each functor and Hom-set and the lower-star preservation hypothesis at the point where the restricted right adjoint is used. If K or L is zero, both the restricted and ambient corresponding Hom-sets are singletons and the same bijection results. For the identity scheme morphism this is the same ambient identity-functor adjunction restricted to the full subcategory. On the empty scheme the derived category is zero, again giving the same singleton Hom-sets. No nonzero coefficient ring or nonempty scheme hypothesis is needed by the restriction theorem. No new statement or source error was found, and no statement correction is proposed.

## Validation and handoff

The final sandbox is checked by the required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q56 def-sfb-dc-upper-lower-adjunction --no-push`; its output determines the READY result. The script checks the delivery in its own temporary worktree. No push is performed by this worker. A fresh second reader must inspect the sources and artifact before delivery. This pass writes only in the assigned sandbox; it runs no direct git command, compiler, Lake or build tool, writes no Lean, and starts no agents.

## Second reading by Q56

- Item source: it names the current blueprint rather than a Stacks tag; no Stacks lemma or forbidden SGA source is used; verdict PASS.
- Item statement: checked verbatim against `def-sfb-dc-upper-lower-adjunction.md` in the main-20261015 blueprint; all hypotheses and both Hom-category directions agree; verdict PASS.
- Original proof paragraph (step 1): checked against `def-sfb-dc-upper-lower-adjunction.proof.md`, the parent restricted-functors proof, and all four dependency statements. Its ambient Hom bijection, full-subcategory Hom identification, and naturality are exactly Mathlib Restrict.lean:44–59; no uncited geometric or preservation fact is used; verdict PASS.
- Dependency `def-sfb-dc-lower-star`: its statement supplies the conditional preservation hypothesis and commutation with ambient inclusions used for the right adjoint; verdict PASS.
- Dependency `def-sfb-dc-upper-star`: its statement supplies preservation and commutation with ambient inclusions used for the left adjoint; verdict PASS.
- Dependency `def-sfb-module-derived-pushpull-adjunction`: its statement supplies the ambient derived adjunction; verdict PASS.
- Dependency `def-sfb-bounded-constructible-complexes`: its statement supplies the bounded-constructible full subcategory and fully faithful inclusion; verdict PASS.
- Mathlib declaration: read `CategoryTheory.Adjunction.restrictFullyFaithful` and its Hom formula in `Mathlib/CategoryTheory/Adjunction/Restrict.lean:42-50,76-85`; the item is a direct specialization with the listed compatibility isomorphisms; verdict PASS.
- New nodes: none; no node statement, proof step, or citation requires review.
- Edge cases: zero objects, the identity on Spec(k) for a field of the stated characteristic, empty schemes, and zero coefficient ring leave the full-subcategory Hom bijection valid; no extra hypothesis is needed; verdict PASS.
- Duplicate search: `rg` over `dag/nodes` and blueprint searches for `upper-lower-adjunction` and `adjunction restriction` found no duplicate statement requiring a new node; verdict PASS.

Changes made in this second reading: appended this independent audit section and recorded three fresh Mathlib searches in the node and search log. LeanFinder used the new object-property phrasing above; Loogle used `CategoryTheory.Adjunction, "FullyFaithful"`; grep used `restrictFullyFaithful|homEquiv := fun` in `CategoryTheory/Adjunction`. Each returned the restriction construction. The statement, leaf designation, dependencies, empty proof and empty citations remain correct and unchanged.

Second-reader validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q56 def-sfb-dc-upper-lower-adjunction --no-push` printed `OK (not pushed) ... at 12f3ad6038: preflight passed`. The installed wrapper accepts exactly the group and item arguments plus `--no-push`; a trailing dot prints its usage, so the supported invocation above was used. Delivery follows with the same reviewed artifact.
