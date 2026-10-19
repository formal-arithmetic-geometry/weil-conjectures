# lem-coef-sharp-filtered-poset-subsets

## Files written

- `dag/nodes/sec-six-functors/lem-coef-sharp-filtered-poset-subsets.json`: statement, now split; statement and statement dependencies preserved. Four proof steps; Mathlib verdict: the entire item is not an exact match or a one-line specialization. Its closure step reuses the already existing Mathlib leaf `lem-coef-small-directed-superset`.
- `citations.json`: three verbatim statement quotations covering all three external-node citations in Steps 1, 2, and 4.
- `report.md`: this report. Search records are in the sandbox's `searches.jsonl`.

There are zero new nodes and zero new Mathlib leaves. One existing Mathlib leaf is reused. The unit and chapter records are unchanged; this item is not their key statement.

## Attachments

None. I searched the project Lean under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, filtered-poset/subset terminology, sharply-smaller/cardinal terminology, `transfiniteIterate`, and the cofinal-family declaration name. The project has no declaration giving this item's clauses. General transfinite-iteration applications in `CategoryTheory/GrothendieckAbelian/SerpeGeneratingSet.lean` are not attachments. The exact upstream master source was checked read-only and was not treated as completed proof evidence.

## Sources wanted

WANTED: Jacob Lurie, Higher Topos Theory, Lemma 5.4.2.8 and Proposition 5.4.2.9, printed pp. 425-426, for lem-coef-sharp-filtered-poset-subsets. The PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf was read online (PDF pages 442-443, zero based); it is not archived under literature/. No download or literature edit was made. The proof is marked agent-written: its cardinal enumeration and family argument are explicit, and the transfinite construction is supplied by the existing checked Mathlib leaf. There is no relevant Stacks tag for this cardinal-directedness assertion, so no unrelated tag was substituted.

## What was wrong or incomplete

The item was a statement-only node. Its statement is correct, including the strict cardinal bounds and empty-family assertion; no statement correction or STATEMENT-DISPUTED is needed. The inherited Mathlib search history correctly warns that Mathlib's categorical `Cardinal.SharplyLT` is not definitionally this cardinal-exponent assumption. A whole-DAG search also found the more useful existing leaf `lem-coef-small-directed-superset`, whose explicit cofinal-family hypothesis can be verified without proving that categorical predicate.

The imported ancestor is `prop-coef-integral-exceptional-adjoint`; I read both its archived master text and the current `main-20261015` proof in `sec-six-functors/sk-thm-sf-package/`. Paragraph 2 concerns the finite-coefficient mapping-complex adjunction. This cardinal lemma occurs far below it as generic accessible-localization infrastructure, through the inherited ancestry and `lem-coef-presentable-cardinal-enlargement`, not as a replacement of that geometric proof. Its old unit/chapter binding is maintainer-owned and has been preserved.

## Source conventions

HTT uses primed and unprimed kappa notation in Lemma 5.4.2.8 and its use in Proposition 5.4.2.9, while the PDF text extraction drops the comparison glyph. I kept the item's explicit convention: alpha is the lower directedness cardinal and beta the upper size cardinal. The proof needs upper bounds only for alpha-small subsets. The existing Mathlib leaf confirms that these hypotheses suffice, without requiring beta-directedness of A. No statement or unit-route correction is needed.

## Not duplicates

No new nodes. In particular, I did not create a second transfinite-closure lemma: `lem-coef-small-directed-superset` already states the construction under a weaker, explicit cofinal-family hypothesis. Nor did I create a counting lemma or a lemma for the family upper bounds: both arguments are written as elementary steps of this item's proof.

The whole-DAG searches included regular-cardinal/union and filtered-subset terminology, the relevant Mathlib declaration names, and `5.4.2.8`. Blueprint searches for filtered poset, filtered subsets, cofinal subset, regular cardinal, transfinite, small directed, and union of sets found no blueprint statement duplicating the item. `blueprint_refs.py ancestor` confirmed the preserved ancestor. Candidates such as `lem-coef-small-family-regular-bound` only choose a large regular bound for an arbitrary small family; they do not state this directed-enlargement result. The statement of every candidate actually used was opened in full.

## Unfinished work

None for this one-level split. No Lean was written, compiled, or built; no shared-repository or launcher file was modified. This delivery stops after the required no-push dry run so that the fresh second reader can review and deliver it.

## Review by NX

I read delivery-errors B through E in full, the worker brief, stage 1, the three blueprint levels in SETUP.md, GOAL.md, dag-sync.md, the item's chapter and unit, its parent enlargement split, and its blueprint ancestor's old and current source texts. I checked the original statement against HTT 5.4.2.8/5.4.2.9 with alpha consistently denoting the lower cardinal. No new nodes require a separate source audit.

For Step 1 I opened the complete statement of `lem-coef-small-directed-superset`. It expressly defines infinite regularity by the small-union property, which is exactly the part quoted in citations.json and used here at beta. The counting is written out rather than hidden: ranges of functions from an ordinal xi cover all subsets of cardinality below alpha, the number for each xi is bounded by the actual exponent mu raised to |xi|, and the alpha indices are fewer than beta. The identity enumeration makes the whole family cofinal. This uses only cardinality as enumeration/injection, exponentiation as the cardinality of a function set, and the stated regularity convention. It therefore creates no lemma for an elementary three-line cardinal count.

For Step 2 I checked the existing leaf's full statement and read its actual pinned Mathlib source, `Mathlib/CategoryTheory/Presentable/SharplyLT/Basic.lean:241-261`, as well as the transfinite construction immediately preceding it. The hypotheses match with sigma=alpha, tau=beta, I=A, S=T. Step 1 establishes the universally quantified cofinal-family condition for every small X of size less than beta, not only for T or A. A is small and is alpha-filtered by exactly the assumed upper-bound condition including the empty subset. Both cardinals are infinite regular and alpha<beta. The leaf concludes containment, size strictly below beta, and alpha-filteredness in the inherited order. These are all clauses the step takes from it; no claim is borrowed from its proof. The leaf is already a Mathlib leaf in the same unit, so no tool-use or route exception is needed.

For Step 3 I verified directly that the collection is a subset of the small power set of A, inclusion is a partial order, singletons have size below beta, and the enlargement of each singleton gives the covering. The empty input T is permitted by Step 2, so the collection is nonempty. This is an elementary consequence of the previous step and universe conventions, not a new external theorem.

For Step 4 the same regularity sentence in the existing leaf's statement supplies the small-union property, with fewer than beta members each smaller than beta. Applying the enlargement already proved in Step 2 to their union gives one member containing every original member. I wrote both containments explicitly. For the empty family its union is empty and the same enlargement applies; for a family with repetitions the set of distinct values is no larger than its index set. Thus the conclusion is the full requested beta-directedness, not just ordinary finite directedness.

I tested the small cases: X empty has precisely the empty subset, obtained at xi=0, with 0^0=1; alpha=aleph_0 permits all finite subsets and still alpha<beta; T empty is not mistaken for an allowed empty filtered B; and an empty A cannot satisfy the original upper-bound assumption because it includes the empty subset. For finite A the assumption supplies a top element, consistent with the construction. I did not use regularity of a singular cardinal or replace a strict bound by a weak one. The actual enumerations include zero domains and empty codomains. These checks required no statement repair.

Every non-elementary construction is the statement of the one cited existing leaf; all remaining operations are the explicit elementary count, powerset restriction, singleton argument, and union containments. The verbatim citation file was generated from that node's statement. The item contains no circular citation, no new restatement of one of its own clauses, no unsplit node with a proof, and no alleged project attachment to Mathlib. All newly recorded Mathlib searches were actually run with msearch.py and read. The inherited searches were retained unchanged, and current queries/results were appended. No unavailable service was called a negative result.

## Second reading by NX

- Item statement: checked HTT Lemma 5.4.2.8 and Proposition 5.4.2.9 (PDF pp. 425–426) hypothesis by hypothesis; the lower/upper cardinal convention is faithful, including regularity, the exponent bound, empty small subsets, inherited order, covering, and the empty family.
- Step 1: checked the range enumeration against the successor-stage size argument in HTT Lemma 5.4.2.8 and the quoted regular-union statement of `lem-coef-small-directed-superset`; the empty domain and $0^0$ case, all $\alpha$-small subsets, and the strict $<\beta$ bound are handled explicitly.
- Step 2: checked every hypothesis and conclusion against the full statement of `lem-coef-small-directed-superset` and its Mathlib declaration at `Mathlib/CategoryTheory/Presentable/SharplyLT/Basic.lean:241-261`; the substitution $(\sigma,\tau,I,S)=(\alpha,\beta,A,T)$ is exact and only the cited statement is used.
- Step 3: checked the powerset smallness, partial-order restriction, singleton covering, and nonemptiness against the item definition and Step 2; the empty poset and empty subset cases are included.
- Step 4: checked the union argument against HTT Lemma 5.4.2.8's final family assertion and the regular-union clause of `lem-coef-small-directed-superset`; distinct-family cardinality, empty families, and both inclusion containments are explicit.
- New nodes: none; consequently there were no new-node statements or Mathlib leaves to audit. The sole cited external node was searched and opened in full, and no duplicate node was created.
- Changes: corrected the node's `created.item` from the parent item to `lem-coef-sharp-filtered-poset-subsets`, which is required for delivery ownership metadata; no mathematical statement or proof step required repair.
