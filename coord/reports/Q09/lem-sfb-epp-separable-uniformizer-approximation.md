## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-epp-separable-uniformizer-approximation.json` (the item, now split), and `citations.json`. The item's statement and statement dependencies are unchanged. Its existing searches are retained, and five actual Q09 searches from searches.jsonl are appended. There were no earlier sandbox node files, report or split to resume.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The live node `lem-sfb-epp-approximate-uniformizer-root` already states the stronger degree-p^r version of every required conclusion. The brief explicitly requires citing an existing generalization rather than making another node. Its proof remains work for its own item; this delivery neither duplicates nor edits it.

Attachments: none. I searched WeilConjectures for the exact blueprint tag and the uniformizer/separable-approximation concepts. No declaration supplies the whole item. DVR root-algebra declarations concern exact root extensions, not this characteristic-p separable perturbation.

WANTED: none.

The initial node had no proof. No mathematical error was found in its statement. The only change needed to use the source's formula is the sign of the error coefficient. No unfinished portion of this one-level split remains.

## Reuse and searches

I read Stacks `more-algebra.tex`, Tag 09EW (`lemma-make-degree-q-extension`), statement and proof, and Tag 09EV (`lemma-pull-root-uniformizer`) for the preceding root-algebra argument. The latter is only a source sanity check, not an additional dependency. I also opened `lem-sfb-eisenstein-quotient-dvr`, `lem-sfb-totally-ramified-uniformizer-presentation`, `lem-per-eisenstein-prime-ideal-criterion` and `lem-per-complete-dvr-finite-normalization`. Those would be ingredients for reconstructing the stronger approximate-root node; that reconstruction is unnecessary here.

The full-DAG searches for 09EW, `lemma-make-degree-q-extension`, Eisenstein and complete DVR statements found `lem-sfb-epp-approximate-uniformizer-root`, whose entire statement was read. It has empty proof dependencies and is not merged, so this reuse introduces no path back to the item. Whole-blueprint searches used `blueprint_refs.py search` with `Eisenstein`, `09EW`, `uniformizer`, `ramified` and `approximate roots`; no imported blueprint node states this algebra result. The stronger node is a recently created supporting node, not an imported blueprint node.

The five msearch commands ran with this item as their logging key: two different LeanFinder phrasings, Loogle, grep and LeanSearch. All services responded. The hits were untilt/perfection approximation results, valuation decomposition, Witt-vector DVRs, Hensel results, purely inseparable field results, separable residue extensions, and Eisenstein results. None states the full item or specializes to it in one line. I read `Polynomial.irreducible_of_eisenstein_criterion` in Criterion.lean, lines 175-180; irreducibility alone is not this item. Exact queries and hit summaries are in the item and searches.jsonl. No unavailable service is described as an empty search.

## Not duplicates

No new-node pairs exist. The item is intentionally proved from the existing more general `lem-sfb-epp-approximate-uniformizer-root`: specialize r=1, h=n. In particular no new statement-only node is used to relabel the item's conclusion.

## Review by Q09

I checked the unchanged statement against Tag 09EW, `lemma-make-degree-q-extension`: the characteristic-p branch gives a separable degree-q extension, a totally ramified integral closure and both approximation formulas; the general existing node explicitly includes the complete-DVR specialization. The item's n>1 agrees with h>1, p is prime, and r=1 satisfies r>=1. The existing node assumes precisely the same complete characteristic-p DVR and uniformizer data, not a perfect residue field or any extra excellence assumption. Finite degree p gives finiteness of the extension as required.

Step 1 uses only `lem-sfb-epp-approximate-uniformizer-root`. I opened its JSON statement and checked, clause by clause, the degree, separability, integral closure, its completeness and DVR property, the unchanged residue field, the ideal-power equality, and the second approximation. Its residue-field equality is the standard identification induced by the inclusion of integral closures, not an arbitrary abstract isomorphism between residue fields. This is the same totally ramified residue identification as in Tag 09EW. The step spells out every substitution and renames the cited node's uniformizer to avoid confusion with the item's base uniformizer. It is marked non-elementary because the existence theorem is the substantial input; no proof hidden in that node is used.

Step 2 uses `def-sc-discrete-valuation-ring`, whose statement explicitly defines a uniformizer by maximalIdeal=tR. This turns the cited ideal and residue statements into the exact displayed clauses of the item. Setting a=-b' is a ring identity; no lifting, coefficient comparison or uncited theorem occurs. The step is elementary, and citations.json quotes the actual uniformizer definition verbatim. It does not cite a definition as a substitute for the existence theorem.

As small-case checks, take R=F_p[[t]], n=2 and p=2 or 3. The source's perturbation polynomial is X^p-t^(n+p-1)X-t, with nonzero constant derivative -t^(n+p-1). Its error term after adjoining a root has s-order p(n+p-1)+1, at least np; the approximation is consistent even at these smallest parameters. In characteristic 2, -b'=b', so rearrangement still gives exactly the item's sign. At larger n the same substitution h=n is valid. No assumption about perfectness of the coefficient field enters. These are source/statement sanity checks, not additional lemmas asserted by this delivery.

I checked delivery-errors B-E against the actual files: no new nodes require extra definitions or proofs; every non-elementary input is the statement of the existing cited node; the quote for each step is verbatim; no original clause or hypothesis changes; and neither proof step reaches 2000 characters. The short specialization avoids the D1/D2 problem by reusing a pre-existing stronger theorem, as required by the duplicate rule, instead of creating a new restatement.

I read the chapter and unit records and the latest blueprint's `sk-thm-sf-ctf-stability` section and proof. The recorded Epp creation chain is historical: the latest direct-image paragraph does not itself assert this auxiliary DVR claim. `blueprint.from.place` and `split_report.blueprint` say this explicitly. The inherited null ancestor is retained, consistent with `blueprint_refs.py ancestor` returning None. No unit/chapter route or maintainer-owned record was edited, and no SGA source is used. This direct-delivery review is my own reading as Q09, not a claim of independent second review.

## Validation

The required deliver.py --no-push completed successfully: server preflight passed, including check_dag and review_split. Both citation quotes were checked against their live node statements. The proof steps have 490 and 453 characters. A final source-tag check corrected the report-only background tag for lemma-pull-root-uniformizer from 09EN to 09EV; neither the item nor its cited dependencies changed.
