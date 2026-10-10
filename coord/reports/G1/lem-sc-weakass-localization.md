1. Files written:

- `lem-sc-weakass-localization.json`: item split into three elementary implications; Mathlib verdict: no match.
- `citations.json`: empty, because all three steps use only the item hypotheses, localization definitions, and the elementary prime correspondence and annihilator calculation spelled out in the steps.

2. Attachments: none.

3. WANTED: none.

4. The item statement was already present in the repository but had an empty proof and an earlier `created.item` value referring to its downstream user; I preserved the statement and corrected the proof split in the sandbox. No new child node was needed: each implication is a short calculation from localization fractions, annihilators, and the prime correspondence, exactly the argument used by Stacks Algebra Lemma 10.66.2 (tag 0566). The source and blueprint were checked through the node's recorded source and ancestor `lem-sc-hilbert-polynomial`; the blueprint place is the induction-step localization characterization.

5. Nothing remains unfinished.

## Review by G1

I checked the item against Stacks Algebra Lemma 10.66.2, tag 0566, including the hypotheses that R is a commutative ring, M is an R-module, and p is prime. Step 1 explicitly checks that a witness remains nonzero after localization, computes its localized annihilator, and uses the prime correspondence below p to obtain minimality and the radical clause. Step 2 uses only the definition of radical and the fact that p R_p is prime. Step 3 writes a localized witness as m/s, removes the unit denominator, computes the annihilator as the extension of Ann_R(m), and contracts a hypothetical smaller prime to contradict minimality. These are the three implications in the source proof, with no unstated hypotheses. Every cited fact is written in the corresponding step; consequently `citations.json` correctly has no node entries. I also checked small edge cases such as m = 0 (excluded by minimality at a proper prime) and a field localization (where the unique prime is the zero ideal). The mandated LeanFinder, Loogle, grep, and unavailable LeanSearch queries were run for the item and recorded in the node's `mathlib_searches`; no Mathlib declaration states weak association in this form.

Blueprint reference: the item realizes the `lem-sc-hilbert-polynomial` proof's induction-step clause, “the localization characterization of weakly associated primes used in Algebra Lemma 10.66.9”; `same_as` is empty.

## Second reading by G1

- Item statement: checked against Stacks Algebra Lemma 10.66.2, tag 0566, including all three equivalent clauses and the hypotheses that R is a ring, M an R-module, and p prime; verdict: matches.
- Step 1: checked against tag 0566 proof of (1) => (2),(3); the annihilator calculation and contraction/extension correspondence are written explicitly; verdict: correct and elementary.
- Step 2: checked against tag 0566 proof that (2) implies (3); radical equal to a prime gives minimality; verdict: correct and elementary.
- Step 3: checked against tag 0566 proof of (3) => (1), with the equivalent clause (2) used here; denominator removal, prime extension, and strictness by contraction are explicit; verdict: correct and elementary.
- New nodes: none; therefore B1-B7 and duplicate-node checks are vacuous. Existing definition nodes cited in the statement were checked to define the two localization notions.
- Edge cases checked: the zero module cannot witness a proper minimal prime; for a field the only prime localizes to itself; for the zero ring there is no prime p, so the statement is vacuous; n is not a parameter of this lemma.

Changes made: rewrote Step 1 to state the fraction annihilator calculation directly, and Step 3 to justify that q R_p is prime and strictly below p R_p by contraction. No statement or source was changed; citations.json remains empty because no external DAG node is used. The recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches were checked against searches.jsonl.
