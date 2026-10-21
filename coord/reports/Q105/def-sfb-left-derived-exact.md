# def-sfb-left-derived-exact — Q105

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-left-derived-exact.json`: existing definition/result, now split into five steps. Mathlib supplies the exact factorization and categorical uniqueness ingredients, but the K-flat-derived existence/interface used by this statement is a project dependency. Statement unchanged.
- `citations.json`: eight verbatim statement excerpts, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file was changed.

## Attachments

None under the brief's criterion of a declaration in `lean/WeilConjectures/` with exactly these hypotheses.

I searched `lean/WeilConjectures/` for the blueprint id, the proposed declaration name and the left-derived/exact notion, then read `WeilConjectures/CategoryTheory/DerivedCategory/LeftDerivedFunctor/MapDerivedCategory.lean:105-139`. Its `CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory` (line 128) has a real body but assumes the three graded tensor families `HasTensor₄ObjExt`, `HasGoodTensor₁₂Tensor` and `HasGoodTensorTensor₂₃`; those are absent from this item's hypotheses. The item's existing Lean record already explains that mismatch. I did not treat its stronger statement as an attachment.

The existing `Sheaf/CategoryTheory/DerivedCategory/LeftDerivedTotalTensorExact.lean:55` comparison and its compatibility theorem were also read. They use exactly the recorded total-tensor interface and are already attached in the item's metadata. Their presence does not meet the brief's explicit upstream-only attachment rule; I preserved that metadata and changed no Lean.

## WANTED

None. All sources used were available locally.

## What was wrong or incomplete

The imported proof condensed existence, localization, recognition on K-flat objects and uniqueness into one paragraph and cited only two definition nodes. In particular it had no node citation for existence of the exact termwise factorization or for uniqueness of derived functors. I replaced that paragraph with five argued steps and citations of existing, already searched nodes. The statement and its hypotheses did not require correction.

I specified the counit direction as `D(F) Q_C -> Q_D K(F)` throughout. This is the inverse of a factorization isomorphism displayed in the opposite direction, as the blueprint intends. I also wrote the chain-homotopy calculation, so that applying localization on `K(C)` does not silently replace the blueprint's homotopy-category source by the category of complexes.

No part of the unit or chapter route was replaced: the parent unit's third step explicitly invokes this node for the left-derived clause of exact functors. I read that unit and the chapter record; no realization fields are due because this item is not the key node of the unit.

## Searches and reuse

I ran and read two LeanFinder phrasings, LeanSearch, Loogle and two Mathlib greps through the prescribed `msearch.py`. Their exact query texts and actual results are in the item and in `searches.jsonl`. All services answered successfully. The hits `mapDerivedCategory`, `mapDerivedCategoryFactors(h)`, `leftDerivedUnique` and `isLeftDerivedFunctor_of_inverts` are ingredients; the item also uses the K-flat left-derived existence and recognition theorem in `def-sfb-left-derived-functor`, which is not a Mathlib declaration. I read the local Mathlib sources rather than counting a name hit as a match for that whole interface.

Before proposing anything new I searched the whole DAG by statement/title for exact derived functors, localization, Kan extension and uniqueness, and used `tools/blueprint_refs.py search` with `left derived`, `exact functor`, `localization universal` and `unique counit`. The ancestor command returned this item's own id. The opposite, right-derived blueprint item is different. The aggregate parent unit contains this assertion as one clause, so is not a `same_as` duplicate of this item. There was no other blueprint node stating exactly this result; `same_as` is now `[]`.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-exact-functor-derived-factorization`, `lem-weil-pbc-localization-universal-property` and `lem-sfb-right-kan-extension-unique-iso`; did not recreate their special cases. I also read `lem-weil-pbc-exact-functor-derived-functor`, which could supply a more general alternative, but kept the blueprint's K-flat-counit recognition argument instead. The similarly named smooth-purity nodes concern triangulated exactness of an already derived functor, not this comparison.

## Review by Q105

I read the current main-20261015 chapter, unit, item statement and `.proof.md` in `sk-def-sfb-derived-categories`. The item retains the precise monoidal abelian source assumptions of `def-sfb-left-derived-functor`; the target is merely abelian. I read Stacks `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`, around line 5884), which justifies preservation of all quasi-isomorphisms and says that the remaining details are omitted. I also read `homology.tex`, Tag 010N (`lemma-exact-functor`, around line 1545), the exactness notion behind that preservation. The additional localization and uniqueness details here are my expansion of the blueprint and are honestly marked `proof_origin.by = agent`; I did not attribute a left-derived statement verbatim to Tag 015F's right-derived statement.

For step 1 I opened the complete statements of `def-sfb-preserves-kflat-quasi-iso` and `def-sfb-left-derived-functor`. The former explicitly asserts that every exact additive functor preserving finite limits and colimits preserves K-flat quasi-isomorphisms; I use that assertion, not its proof or just the definition of the predicate. The latter explicitly gives the total left derived pair under exactly the hypotheses the item imports. These are all satisfied here, including source coproduct and colimit conditions. The new text fixes the homotopy-category source and names its counit.

For step 2 I read `lem-weil-pbc-exact-functor-derived-factorization` and `def-weil-abstract-derived-category`. The first explicitly states preservation of every quasi-isomorphism by the termwise functor, which is precisely the clause used; I do not take a homotopy-category comparison from its proof or from its Mathlib match. The second explicitly allows localization of `K(C)` at images of quasi-isomorphisms. The only intermediate argument is written out: applying an additive functor to the chain-homotopy equation again gives a chain homotopy. This needs no preservation of infinite coproducts by F, and does not require that F send K-flat objects to K-flat objects. The step consequently proves that `Q_D K(F)` inverts the arrows localized by `Q_C`.

For step 3 I read every clause of `lem-weil-pbc-localization-universal-property`. Clause (1) supplies the actual functor and factorization with the required counit direction; clause (2) supplies compatible uniqueness of that factorization. Its statement permits an arbitrary localization, not only a small-index colimit construction. I instantiate it with `K(C)`, its quasi-isomorphism class, `D(C)`, and target `D(D)`; these categories use the project's existing chosen universes. The termwise interpretation is the displayed component of its factorization. No new identification theorem is hidden here.

For step 4 I reread the final sentence of `def-sfb-left-derived-functor`: its converse applies to a candidate functor with counit invertible on all K-flat complexes. The counit just constructed is invertible on every complex, hence on this subclass. The F and source assumptions are exactly those of step 1. The recognition assertion is explicitly cited, not declared elementary.

For step 5 I opened `lem-sfb-right-kan-extension-unique-iso`, including its explicit counit-compatible equation and absence of a smallness assumption. I checked its Mathlib source `Functor/KanExtension/Basic.lean:134-145`, as well as `Functor/Derived/LeftDerived.lean:54-64,136`, which identifies total left derivation with a right Kan extension. Taking its R to be LF and S to be D(F) gives the comparison in the stated direction and the equations printed in the step. Both pairs extend the same functor on the same homotopy category. Thus canonicity is relative to the fixed counits, as required, and not an unsupported assertion that there is only one isomorphism of their underlying functors.

I checked B through E of `coord/delivery-errors.md` point by point against these files. There are no new statement-only nodes, duplicated nodes, extra notions without a source, unperformed searches, hidden clauses moved into children, or source/hypothesis changes. Every non-elementary inference has its supplying node, and every citation was checked against the statement (C1/C4); the excerpts in `citations.json` are copied without normalization. No step exceeds 2000 characters. All dependencies are existing unmerged nodes; the generic off-unit tools are already Mathlib leaves, so no route exception is needed.

I tested the construction on the zero functor and on the identity exact functor: both factorization counits are invertible and the uniqueness equation has the expected comparison. For a general exact F, D need not be monoidal and F need not preserve coproducts or K-flat objects; none of those hypotheses enters the argument. Unbounded complexes cause no boundedness assumption to appear, and no projective/injective resolutions are substituted for the unit's K-flat route. There is no statement dispute.

## Unfinished work

None in this one-level split. The existing left-derived existence/recognition dependency remains another item's responsibility; I have not split it or copied its proof into a new node. Required server validation and direct delivery follow this report.
