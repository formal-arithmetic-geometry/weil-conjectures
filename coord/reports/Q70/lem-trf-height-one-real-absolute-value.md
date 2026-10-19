# Stage-1 report: lem-trf-height-one-real-absolute-value

## Files written

- dag/nodes/sec-trace-formula/lem-trf-height-one-real-absolute-value.json: statement, split; unchanged hypotheses and conclusion; eight proof steps.
- dag/nodes/sec-trace-formula/lem-trf-archimedean-group-real-embedding.json: statement, Mathlib leaf; Archimedean.exists_orderAddMonoidHom_real_injective, Mathlib/Data/Real/Embedding.lean:234–242.
- citations.json: verbatim statements for every step/node citation.

One new node, one Mathlib leaf. The unfinished earlier helper lem-trf-height-one-value-group-archimedean was never delivered and is removed from this sandbox: its short bounded-subgroup argument is now Step 3 itself. The earlier exponential construction, blueprint provenance, and all original searches.jsonl entries are retained; inaccurate search summaries and unlogged claims in the provisional new-node metadata were replaced by actual recorded searches.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the item tag and for height-one, Archimedean, prime/convex, and embedding terminology. Padic and divisor results do not state this general height-one valuation theorem. There is no attachment for either the item or the new ordered-group leaf. Upstream master is reference material only.

## Wanted literature

WANTED: local literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, §2.1, printed pp. 6–7, for the item. The named local PDF is absent, and the author-hosted PDF timed out, but the same v3 paper was read online at https://arxiv.org/pdf/0707.3953, specifically printed p. 7. No download or repository write was made. Stacks algebra.tex, Tags 00I9, 00IB, 00ID, 00IE, 00IF and the inverse characterization immediately after 00IB were also read locally. The proof is marked agent-written: Temkin gives the valuation conventions and correspondence, while the ordered-group and exponential argument is supplied here.

## Corrections and route

The item statement is true and unchanged. The provisional helper merely isolated its height-one intermediate claim; its content is a few-line argument with the explicitly constructed bounded subgroup and belongs in the item's proof. The previous zero-case explanation incorrectly attributed positivity to injectivity: positivity comes from exp(t)>0, whereas injectivity is used for reflecting order. The proof now distinguishes those roles and deals separately with zero, cancellation, and the maximal ideal. The latter is identified by constructing the positive-value ideal, rather than silently using a local-ring criterion not stated by the cited definition.

The chapter and unit were read: sec-trace-formula and sk-i-curve-zero. This is the historical valuation-normalization ingredient already assigned to this node, not a replacement for the unit's current contracting-correspondence route. Its existing blueprint ancestor and via list are retained. No chapter or unit is changed; no additional off-route theorem is introduced. The existing correspondence lies in the same unit; the new generic embedding is a Mathlib tool.

## Not duplicates

lem-trf-archimedean-group-real-embedding vs def-trf-totally-ordered-abelian-group: the existing node defines an ordered group, while the new leaf asserts an injective real embedding under the additional explicitly defined Archimedean property.

lem-trf-archimedean-group-real-embedding vs lem-trf-valuation-prime-convex-correspondence: the existing theorem relates valuation prime ideals to convex subgroups and makes no real-embedding assertion.

lem-trf-archimedean-group-real-embedding vs lem-trf-height-one-real-absolute-value: the leaf is a theorem about arbitrary Archimedean ordered groups, with no field, valuation ring, absolute value, or ball identification; the item constructs and verifies those additional structures.

The whole DAG was searched for the declaration, Archimedean-group and real-embedding concepts; whole-blueprint searches for Archimedean, height one, convex subgroup and ordered group gave no equivalent blueprint statement. The existing prime/convex theorem was opened and reused. No new Stacks-tagged node is introduced. Real-power, l-adic, and discrete valuation results are different hypotheses/objects.

## Review by Q70

I read the item, chapter, unit, current repository version, existing partial sandbox, citations, and searches.jsonl. I checked delivery-errors B–E against the actual files, including self-contained statements, exact quotations, elementary arguments, nonduplication, source places, and hypotheses. The new leaf is statement-only and its statement defines Archimedeanness explicitly. Its source was read at Mathlib/Data/Real/Embedding.lean:29 and 232–242; in particular the `omit` line removes the otherwise apparent need for a chosen positive 1. LeanFinder, Loogle, grep, and LeanSearch really ran via msearch.py; their results are recorded with the exact query texts, with both semantic phrasings yielding the matching declaration. The item retains the current repository's prior searches and its sandbox's actual searches. None of the removed helper's unlogged search claims remains in a delivered node.

Step 1 cites def-trf-valuation-ring only for its explicitly stated x-or-inverse alternative. It writes the quotient-order checks itself; it does not take a theorem about value groups from that definition. Step 2 cites lem-trf-valuation-prime-convex-correspondence precisely for its stated anti-isomorphism with the same y/x order. I opened that node and checked its field, valuation-subring and ordered-quotient hypotheses: all are present. The two distinct primes force exactly the two endpoint convex subgroups. Step 3 writes the bounded subgroup, its closure, convexity, and consequence in full, using only Step 2 and ordered-group arithmetic. There is no imported non-elementary lemma hidden there.

Step 4 cites the new embedding leaf for exactly its injective monotone additive map; Steps 1 and 3 supply all hypotheses. Order reflection follows from totality plus injectivity as explicitly written. Step 5 uses the elementary real exponential identities on this map and proves positivity, normalization, and multiplicativity, including a zero factor. Step 6 cites the valuation definition only for the subring setting and checks the inequality by dividing the sum by its smaller-value summand; cancellation and zero summands are separate cases. Step 7 uses previous steps to construct the positive-value ideal, shows its complement consists of units, and identifies it with the given maximal ideal by maximality. Step 8 cites precisely the x-or-inverse clause again, choosing z outside V to produce a nonzero nonunit and hence a value strictly between 0 and 1. Every `uses` entry has its cited statement copied verbatim in citations.json.

I tested the statement on a DVR (Gamma=Z, uniformizer has absolute value strictly below 1), a nondiscrete rank-one valuation (e.g. rational or dense real value group, where the proof needs no least positive value), the excluded field case (zero group and trivial valuation), and a rank-two lexicographic group (the bounded subgroup is then proper, so the two-prime hypothesis correctly fails). The embedding leaf includes the zero group: Mathlib handles it separately and no nontriviality hypothesis is missing. The item is characteristic-independent. Temkin's multiplicative order is opposite our additive value order, and the minus sign in exp(-e(v(x))) restores exactly his unit-ball convention. No statement dispute was found.

All steps have fewer than 2000 characters. None introduces a non-elementary comparison or omitted standard construction; the only substantial external tools are the cited prime/convex theorem and Mathlib real embedding. No Lean was written and no compiler/build tool was run.

## Unfinished work

None in the authorized one-level split. The new Mathlib leaf needs no further split. The existing correspondence keeps its own current proof dependencies and is not edited.
