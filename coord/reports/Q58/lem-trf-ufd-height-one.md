# Q58: lem-trf-ufd-height-one

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ufd-height-one.json`: existing statement, now a Mathlib leaf. Exact declaration `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one`, `Mathlib/RingTheory/Ideal/UFD.lean:87–89` (Stacks 0AFT).
- `citations.json`: empty list, because a Mathlib leaf has no proof steps or step citations.
- `searches.jsonl`: actual search-command results, including unsuccessful broad and malformed Loogle queries and the successful focused query. No new nodes.

## Attachments

None. Searches in the reference project's `WeilConjectures/` for the blueprint tag, height-one terminology, UFD and factorization did not find an exact project declaration of both implications. Its `UniqueFactorizationMonoid.of_forall_isPrincipal_of_mem_minimalPrimes` in `WeilConjectures/Mathlib/RingTheory/UniqueFactorizationDomain/Kaplansky.lean:94` is a different, one-direction criterion; it is not an attachment of this item. The exact declaration found is in Mathlib and is delivered as a leaf as required.

## Wanted

None; all sources needed were available locally.

## Findings and corrections

The inherited no-match verdict missed the exact theorem. Q58's broad semantic searches returned PID and Dedekind results, which require stronger assumptions, but a grep within `RingTheory/Ideal` exposed `UFD.lean`, and a focused Loogle search confirmed the complete theorem. The final grep gives line 87 and the Stacks annotation at line 86. The original three inherited search entries have been retained as requested; Q58 adds only queries actually executed, with their actual results and accurate verdicts. Invalid natural-language Loogle patterns are identified as invalid, not evidence of absence. Intermediate searches for 034T and 00KV were exploratory; no intermediate nodes were created.

The statement is true and agrees with Stacks 0AFT in `literature/stacks-project/algebra.tex:29459–29483`, with tag/label verified in `tags/tags`. No statement dispute or statement change is required. Statement dependencies and all protected metadata remain unchanged. The existing Noetherian definition node was opened: it says every ideal is finitely generated and is itself a Mathlib leaf. UFD, height one, integral domain and principal ideal are expressed inline or in their usual elementary algebraic sense; no new definition is needed.

## What remains unfinished

Nothing in this stage-1 item. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes. Whole-DAG tag/keyword searches and `tools/blueprint_refs.py` searches for `characterize-UFD-height-1`, `height one prime principal`, `UFD`, `unique factorization`, and `height-one` found no blueprint node stating this equivalence. The `unique factorization` hit is a categorical factorization statement about coextension, unrelated to this item. The parent's regular-local UFD theorem imposes different ring hypotheses and includes parameter and localization-unit clauses; it is not this equivalence.

## Review by Q58

I read Stacks 0AFT and its proof in `algebra.tex`, together with the adjacent 034R and 034T arguments and the 00KV principal ideal theorem. I also read the chapter and unit records and the current main-20261015 proof of the blueprint ancestor. This item is the auxiliary height-one criterion already used by the accepted regular-local UFD argument, not the unit's key statement; no unit record needs editing. Mathlib's exact Stacks-tagged theorem closes that auxiliary item without changing the route.

I read the complete Mathlib `Ideal/UFD.lean`, especially its variable hypotheses (line 26: commutative ring and domain; line 67: Noetherian) and equivalence at lines 87–89. There is no local, regular, integrally closed, dimension-one or Dedekind assumption. Its right side quantifies over every prime ideal of height one and says it is principal, exactly as the item's clause (ii). `Ideal/Height.lean:29–44` defines height of a prime by lengths of strict prime chains. Since zero is prime and is below every ideal in a domain, height one is exactly nonzero with no intermediate prime: a strict intermediate prime would produce a chain of length two, and without one the chain from zero has the maximum length one. This is a direct reading of the same height notion, not a separate comparison theorem. `UniqueFactorizationDomain/Defs.lean:121–143` explicitly explains the usual multiset factorization property underlying `UniqueFactorizationMonoid`; the item's prime-factor and uniqueness wording is the standard same property. Multiplying a chosen factor by a unit converts associated products to a unit times a product, and units use the empty product. Thus every clause and hypothesis matches the Mathlib theorem.

I checked delivery-errors B1–B10: no new nodes or proof-bearing unsplit statements; the item remains self-contained, uses its correct Noetherian definition, preserves TeX, and has its verified exact declaration, file and lines. Searches are retained verbatim from the log, and no source was missing. A Mathlib match is not misreported as a project attachment. For C1–C8 there are no proof steps whose citation or hypotheses could be wrong, and no off-unit theorem edges or cycle were added. `citations.json` is accordingly empty. For D1–D5 no clause was relabelled as a child node and no proof obligation moved elsewhere: the existing Mathlib theorem gives the whole statement. For E1–E7 I compared all ring hypotheses and notions above, with no silent strengthening, object identification, denominator clearing or source correction. There are no long non-elementary steps to audit.

Small cases: a field has no height-one primes and is a UFD (every nonzero element is a unit); in Z height-one primes are the principal ideals (p); in k[x,y] the height-two maximal ideal (x,y) is not required to be principal. The non-UFD Z[sqrt(-5)] does not force all height-one primes to be principal, consistently with the criterion. The zero ring is excluded by the integral-domain hypothesis. These cases confirm that no local or global dimension-one assumption has been introduced.

## Dry-run repair

The first server preflight required a non-null proof_origin even for the item delivered as a Mathlib leaf. I supplied its already verified Stacks 0AFT source and noted the exact Mathlib implementation; status remains mathlib and proof/proof_deps remain empty.
