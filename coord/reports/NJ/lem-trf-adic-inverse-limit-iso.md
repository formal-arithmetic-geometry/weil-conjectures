# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-adic-inverse-limit-iso.json: statement, now split into three elementary tuple calculations; Mathlib search found supporting APIs, no direct completion-tower ring-equivalence theorem.
- citations.json: a verbatim statement quote from the existing completion definition for each proof step.
- report.md: this report. No new nodes, no Mathlib leaves, no unit changes.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, AdicCompletion, adicCompletion, inverse-limit and completion/isomorphism terminology, including CategoryTheory. No project declaration supplies all clauses. The item has no recorded Lean declaration or open sorry decomposition. Upstream master is not being treated as finished proof evidence.

## WANTED

None: literature/stacks-project/algebra.tex contains the definition used.

## Statement and citation corrected

STATEMENT-DISPUTED: the imported sentence "It is the unique map whose composite with every quotient projection is e_n" is ill-typed literally. The composite of a map out of the completion with a projection has domain the completion, whereas e_n has domain A/I^n. It now says p_n^B composed with E equals e_n composed with p_n^A. This specifies the same intended canonical map, and adds no hypothesis. For example, for A=B=Z and I=J=(2), e_1 has domain Z/2 while p_1 E has domain the 2-adic completion: they cannot be equated without p_1 on the right.

The imported pointer "Tag 00MA(3), inverse-limit description of completion" was inaccurate. I read 00MA (algebra-lemma-completion-tensor): its part (3) identifies finite-module completion with a tensor product under Noetherian hypotheses. This item uses none of that. The opening of Tag 00M9 (algebra-section-completion), lines 22529 ff., defines completion by compatible tuples; I cite it and mark the tuple proof agent-written. Stacks' ring convention is the commutative-ring convention of the existing definition; nothing requires Noetherianity, finite generation, completeness of A or B, or a ring map A -> B lifting the e_n.

## Searches and reuse

The sandbox initially had only dispatcher brief markers, no item, proof, report, citations, or search log. The item was read from the shared repository; all writes are confined to this sandbox. The command-created searches.jsonl is retained, and mathlib_searches records its exact queries and observed results. The two semantic phrasings distinguish a completion functor applied to a single original-ring/module equivalence from arbitrary compatible quotient-level ring equivalences. Read Functoriality.lean:179-191 (AdicCompletion.congr), Algebra.lean:361 ff. (liftRingHom) and :434 ff. (ofAlgEquiv). The former uses a common base ring and ideal and an equivalence before completion, the latter assumes an already complete ring. Neither states this lemma. LeanSearch's Ring.DirectLimit hits concern colimits. The second LeanFinder search returned InverseSystem.invLimEquiv and its product-presentation variants; their displayed types require equivalences to initial-segment products and do not apply to arbitrary quotient towers. A Loogle query rejected an identifier; it is recorded unavailable, not used as evidence of absence.

Whole-DAG searches included 00M9, compatible isomorphisms, inverse-limit/ring-isomorphism phrases, and completion terminology. tools/blueprint_refs.py search was run for "inverse limit", "adic completion", and "isomorphism of limits"; none states this tuple lemma. The existing def-weil-pbc-adic-completion already gives exactly the compatible-tuple description and componentwise ring operations needed, so I cite it rather than introduce category-theory or inverse-system nodes. The chapter and sk-i-curve-zero unit records were read, as were the ancestor and direct citer lem-trf-completed-local-base-change. This is the elementary algebraic passage in that existing route, not a replacement for a unit's geometric argument.

## Not duplicates

No new nodes. The completion definition is reused unchanged. The item has no same-as blueprint statement among the searches above.

## Unfinished work

None in the split. No Lean was written and no compiler, Lake, or build was run. Server dry run and delivery are recorded below when complete.

## Review by NJ

I read the item against Stacks algebra-section-completion (00M9), its first two paragraphs, and read the entire statement of def-weil-pbc-adic-completion. That definition explicitly says that completion is the ring of compatible sequences with componentwise operations. This is exactly what each of the three steps takes from it; citations.json quotes that sentence verbatim. There are no other proof citations and no new nodes to compare with external lemmas.

Step 1 introduces both transition maps with their domains, then uses the assumed square b_nm e_n = e_m a_nm to prove the image tuple is compatible. The equality is evaluated on an arbitrary compatible tuple, so it does not assume a lift to A or to B. Preservation of 0, 1, addition and multiplication holds at every coordinate because e_n is a ring isomorphism. The projection formula is the actual displayed coordinate formula, not a claim of unspecified naturality.

Step 2 derives the inverse transition square by composing with the two inverse isomorphisms on the indicated sides. This gives compatibility of the inverse tuple without an additional lifting or exactness lemma. Both inverse identities are checked on coordinate n using the inverse identities of e_n. Equality of compatible sequences then supplies equality of maps. Step 3 checks uniqueness on every coordinate for every tuple, with the correctly typed projection formula; it works even for functions without an assumed ring structure. All three are elementary calculations from the cited definition and the hypotheses, with no hidden limit-exactness, Mittag-Leffler, or adic-completeness theorem.

I checked B1-B10 and C1-C8: no fresh statement-only helper, no duplicate or relabelled clause, no missing notion, no unsupported citation, no circular dependency, no off-unit theorem use, and no unrecorded Mathlib search. D1-D5 are addressed by carrying the entire argument in the item's own steps; no claim is moved into a new node. For E1-E7, the proof only requires the stated compatible isomorphisms for all positive levels and the tuple description; all indices satisfy 1 <= m <= n. Testing I=J=0 gives constant towers and the expected ordinary ring equivalence. Testing I=A, J=B gives the zero limits; nonseparated rings and infinitely generated ideals still work because the argument never identifies A with its completion or a quotient of completion with the original quotient. These cases also show why stronger completion or finite-module hypotheses must not be imported from 00MA. No step is longer than 2000 characters. The repairs made are the typed uniqueness clause and the corrected source pointer described above.
