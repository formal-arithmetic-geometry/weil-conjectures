## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-weakass-minimal.json: existing statement split in four steps; no exact Mathlib match.
- citations.json: a full verbatim statement quote for each of the five step/node citation pairs.
- report.md and searches.jsonl: report and actual Q39 search log.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searches of lean/WeilConjectures for the blueprint id and weak-association terminology found no declaration stating this result. The existing Sheaf weak-association definition and localization criterion are supporting declarations, not attachments for the item.

WANTED: none.

The item statement is correct as written and was preserved, including its absence of Noetherianity and finiteness assumptions. Its original proof was empty. I supplied Stacks 0EMA's argument, with the localization details and reverse inclusion written out rather than hidden in the final sentence of the source. I retained the existing searches and added the actual Q39 searches, including a second semantic phrasing. Read Mathlib's associated-prime definitions in Ideal/AssociatedPrime/Basic.lean:55-110: these use prime radicals of annihilators and do not replace weak association in an arbitrary ring. The minimal-prime hits are definitions or dimension-zero special cases; the associated-prime localization hit assumes Noetherianity. No exact match was found.

Blueprint search: blueprint_refs.py search for 'weakly associated', 'reduced weak', and '0EMA' returned no blueprint node; rg in the entire latest blueprint for WeakAss/weakly associated/0EMA returned no match. The existing item has blueprint.from.node null, and blueprint_refs.py ancestor prints None. Its inherited place and via chain were preserved. I read the current latest sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md: the inherited alteration wording is older than the current direct-images proof, whose (3) now assembles proper and open direct images. This algebraic prerequisite is used by the existing normalization chart argument, and this delivery changes no higher-level statement, route or unit record.

Unfinished work: none for this one-level split. The independent existing criterion lem-sc-weakass-localization remains its own node; no proof of it was moved into this item.

## Review by Q39

I read algebra.tex, label lemma-reduced-weakly-ass-minimal (Tag 0EMA), including its reduced local-ring proof, and label lemma-weakly-ass-local (Tag 0566), including the equivalence used with M=R. I also read the weakly-associated definition immediately before it (0547). No new nodes need source checks. I opened every node actually cited and copied its statement into citations.json, not its proof or a neighbouring declaration.

Step 1 uses def-weil-pbc-localization-at-prime exactly for its fraction equality and the local ring R_p with maximal ideal pR_p. Reducedness is proved explicitly: ua^n=0 gives (ua)^n=0 and hence ua=0. Nonzeroness follows from 0 lying in every proper prime. This is a short elementary fraction calculation, not a hidden localization-preserves-reducedness lemma.

Step 2 uses lem-sc-weakass-localization precisely for implication (1) to (3), producing a localized element whose annihilator radical is pR_p. Its statement has arbitrary R and M and a prime p, so neither finite generation nor Noetherianity is needed. M=R has the usual localized regular module, identified with R_p by the explicit identical fraction formulas. The other citation, def-weil-pbc-localization-at-prime, supplies properness of the maximal ideal. The radical notation is defined inline.

Step 3 is the core calculation of 0EMA, written as a fraction dichotomy to avoid importing an uncited theorem on nonunits of local rings. If the numerator avoids p, the inverse fraction is displayed and the annihilator radical is zero. Otherwise x lies in the annihilator radical, and a power of x kills x, contradicting reducedness and properness. Every assertion follows in a few lines from the setup of steps 1 and 2; it is marked elementary. No general theorem asserting the item's conclusion is cited or made into a child node.

Step 4 uses clause (1) of lem-weil-pbc-primes-of-localization, whose statement explicitly gives an inclusion-preserving bijection with inverse extension, to rule out any smaller prime after pR_p=0. It uses def-sc-weakly-associated-primes for the reverse witness 1, whose annihilator is zero. These statements say exactly what is taken from them. The only off-unit non-Mathlib theorem is the localization criterion; it is declared in split_report.tool_uses as a generic commutative-algebra tool. The other off-unit citations are definitions or Mathlib leaves.

I tested the argument on a field, a non-Noetherian domain, k times k, and k[u,v]/(uv). The two component primes in the last two examples are allowed, with no global-domain assumption. The zero-ring case is handled before choosing a prime. The excluded nonreduced example k[e]/(e^2) fails precisely the nilpotence step. No finiteness of minimal primes, excellence, dimension bound, or finite generation enters. B--E checks: self-contained original statement and explicit notions retained; correct Stacks tags and labels; all cited statements checked for C4; the only non-elementary facts are the cited criterion and prime correspondence (C1); no duplicate, clause-copying node, circular argument, or unsupported transport claim was introduced. All four steps are under 2000 characters. No SGA source, Lean writing, compilation or repository write was used.
