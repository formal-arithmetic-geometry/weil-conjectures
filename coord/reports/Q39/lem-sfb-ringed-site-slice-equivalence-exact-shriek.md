# Q39 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-slice-equivalence-exact-shriek.json: statement node, split by reuse of an existing stronger same-unit result; no exact Mathlib match.
- citations.json: verbatim statement excerpts for each proof citation.
- report.md: this report. searches.jsonl was produced by the required msearch command.

Zero new nodes; zero new Mathlib leaves. The sandbox initially contained no nodes or report, so the current repository item was copied before editing.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, the node id, lowerShriek/lower_shriek and slice-equivalence terminology found no declaration giving this general ringed-site criterion. Scheme/etale lower-shriek results do not cover arbitrary sites. No Lean was written and no compiler or build tool was run.

## WANTED

None. All mathematical sources used are present locally.

## Existing-node reuse

lem-sfb-ringed-site-slice-equivalence-exact-shriek is a specialization of the already existing lem-sfb-local-slice-module-shriek-exact. Both assume continuous/cocontinuous u, preservation of fibre products and equalizers, and equivalences on all ringed slices. Both conclude an additive exact module left adjoint; the existing node additionally identifies its underlying abelian functor. This is existing-node reuse, not creation of a node restating the item. No existing node other than the assigned item is edited. The existing dependency closure has 121 nodes and does not contain this item, so the new edge introduces no cycle.

## Not duplicates

No new nodes were created. The duplicate search is the reason for the short proof: the full statement already exists as lem-sfb-local-slice-module-shriek-exact. That node remains the single reusable prerequisite. The blueprint searches for lower shriek, slice, ringed site and lower shriek exact found no imported blueprint node stating this general ringed-site criterion; hence same_as remains empty.

## Problems found and corrections

The statement is correct and unchanged. The original node had no proof. The two independently created exact-shriek nodes overlap; citing the existing stronger node avoids manufacturing a second set of prerequisites. No statement dispute, missing hypothesis or route error was found. The item's inherited blueprint.from.node is null; this inherited ancestor metadata was preserved, while its existing precise from.place and via list were retained. No stage-2 activity or SGA source was used.

One guessed Mathlib grep path, CategoryTheory/Sites/Cocontinuous.lean, does not exist locally although msearch reported zero hits. I did not interpret that as absence: I ran the corrected CategoryTheory/Sites search, read its hits in CoverLifting.lean, and recorded the distinction in the search verdict. All seven new search records reproduce commands that actually ran; prior search records are preserved.

## Review by Q39

I read Stacks sites-modules.tex at lemma-lower-shriek-modules (0797), remark-when-shriek-equal (0798), and lemma-exactness-lower-shriek (04BH), including their proofs and the comparison equation on localizations. They explain why the reusable criterion is true: 0797 constructs the module adjoint, 0798 compares it with abelian lower shriek after testing the restricted ring on each slice, and the slice equivalence makes that canonical comparison invertible; 04BH gives exactness from preservation of fibre products and equalizers. I did not import terminal-object preservation, which 04BH does not assume, or identify module lower shriek with abelian lower shriek without the slice hypothesis. I also read the latest blueprint unit and its direct-image proof, and the chapter/unit records. This is its inherited supporting site-theoretic lemma and does not replace a geometric route step.

For step 1 I opened def-pur-localized-ringed-site and read its entire statement. It explicitly gives the induced topology and the sectionwise restriction O_U(V/U)=O(V). Thus the two restricted rings agree after precomposition at every arrow c' -> c, including all restriction homomorphisms. I compared these and the remaining item hypotheses with the entire statement of lem-sfb-local-slice-module-shriek-exact: all are identical. This step is elementary: it compares definitions and assumptions, without claiming exactness or existence of an adjoint.

For step 2 I opened lem-sfb-local-slice-module-shriek-exact and read its entire statement, source, dependencies and searches. Its conclusion literally says that T has an additive exact left adjoint L. Its T is the same precomposition on modules, not the right adjoint of it or a scalar-extension functor with a different ring map. Its ring R' is R composed with u and its structural map is identity, precisely as verified in step 1. Its small-site convention is identical. The extra abelian comparison is unused. The adjunction and exactness phrases unpack exactly to the two clauses required in the assigned statement. This application is marked non-elementary and cites the existing theorem rather than silently treating Stacks as a DAG dependency. Every citation has a verbatim quote in citations.json.

I tested the assumptions and conclusion when u is identity, when R is the zero ring, when the domain site is empty, and without assuming a terminal object. Identity gives an identity adjoint; zero coefficients give zero module categories; an empty domain gives the zero left adjoint; the absence of a terminal-object assumption is explicitly allowed in the cited theorem. Neither split step exceeds 2000 characters. There are no newly stated lemmas to test, no unsplit new proof sketches, no new tagged duplicate pairs, no uncited non-elementary transition, no altered target, and no dependency cycle. I checked delivery-errors B through E against these files: self-contained unchanged statement, precise sources, honest searches, direct statement citations, and existing-node reuse instead of relabelling a new clause-node. There is no unfinished mathematical work for this item; the cited unsplit theorem remains independently queued under its existing id.

## Validation

The required server dry run exited 0 and printed OK (not pushed) at c42ed8f4387: preflight passed. The delivery tool ran the server preflight, including check_dag and review_split. A final dry run is performed after recording this result, followed by the authorized direct push.
