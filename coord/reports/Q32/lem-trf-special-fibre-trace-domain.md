# Stage 1 report: lem-trf-special-fibre-trace-domain

## Files written

- `item.json`: split statement with six proof steps and existing-node dependencies.
- `citations.json`: verbatim statement excerpts for every proof citation.
- No new DAG nodes; all required facts were already present in the imported DAG.

## Attachments

No exact sorry-free Lean declaration was found in `WeilConjectures/` of either reference source. The item remains a natural-language split.

## WANTED

None. The Varshavsky PDF and the current blueprint provide the route; supporting facts are existing DAG nodes.

## Review by Q32

I read the item source (Varshavsky, Theorem 2.1.3(b), with §§1.3–1.4) and the blueprint proof of `lem-trf-local-term-locality`, whose second proof paragraph explicitly routes through specialization to the normal cone. I read every statement cited by the six steps. Step 1 uses the Rees/functorial-geometry statement for the special fibre and lifted correspondence, together with the normal-cone definition. Step 2 uses the same node's separated finite-type lift clause and the fixed-scheme fibre-product definition; the remaining product/base-change closure is the direct scheme-theoretic construction. Step 3 uses Nagata compactification exactly for separated finite-type maps and the finite-type dimension lemma for the finite-dimensional compactifications. Step 4 checks the specialization definition, the zero-section theorem's bounded constructible finite-Tor conclusion, and the pro-etale constructible-origin equivalence. Step 5 checks the ambient relative adjunction, finite-Tor preservation, and the package's finite-stage composition/compact-support/exchange clauses, including their stated domain restriction. Step 6 checks that the specialized admissible correspondence and its fixed scheme fit the trace-class definition and therefore yield a Verdier trace class. I verified that every `uses` entry is a node whose quoted statement supplies the sentence used, and corrected the imported creation metadata (which named Q07 and another item) to Q32 and this item. I also ran two phrasings each of LeanFinder, Loogle, grep, and LeanSearch; all returned only generic Mathlib declarations or no match, so no Mathlib leaf or duplicate node was introduced.

## Not duplicates

No new nodes were created, so no duplicate pairs arise.

## Source error

None found in the audited statement or route.
