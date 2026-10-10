1. Files written:

- `pqf-lem-going-up.json`: statement, Mathlib status, and Mathlib search records; no new nodes.
- `citations.json`: empty because the item is a Mathlib leaf.

2. Attachments: none.

3. WANTED: none.

4. The imported proof was a prose reconstruction of going-up. Mathlib already states the needed result in `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` (Mathlib/RingTheory/Ideal/GoingUp.lean:307), so no auxiliary node or proof step is required. No project declaration with the blueprint tag or an equivalent sorry-free declaration was found in `WeilConjectures/`.

## Review by M1

I read the item node and its blueprint source, and checked the exact hypotheses: an integral algebra structure on the map, primes `p ≤ p'` in the source, and a prime `q` whose contraction is `p`. I also read Mathlib's theorem at `Mathlib/RingTheory/Ideal/GoingUp.lean:307`; it assumes an integral algebra, a prime `P`, a prime `I`, and `I.comap ≤ P`, and returns a prime `Q ≥ I` with `Q.comap = P`. Substituting `P = p'` and `I = q`, the contraction equality and `p ≤ p'` give the required inequality, and each returned clause matches the item. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; LeanSearch was unavailable and is recorded as such, while the grep and LeanFinder matches were read in source. The item is therefore marked `mathlib` with the declaration, file, and line recorded. There are no proof-step citations or new statements to audit, and I tested the specialization on the equality case `p = p'` as well as the strict-inclusion case.

## Second reading by M1

- Item statement: checked against Stacks Algebra, Lemma `lemma-integral-going-up` (Tag `00GU`), lines 7853--7877 in the local `algebra.tex`; the integral ring map, prime inclusions, lying-over prime, containing prime, and target contraction all agree hypothesis by hypothesis. Verdict: correct.
- Mathlib leaf metadata: checked against `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` in `Mathlib/RingTheory/Ideal/GoingUp.lean:307`; taking `P = p'` and `I = q`, `q.comap = p ≤ p'` is exactly the theorem's hypothesis, and its output supplies primality, containment, and `Q.comap = p'`. Verdict: exact one-line specialization.
- Proof steps: none (the node is a Mathlib leaf), so there are no uncited dependencies or elementary-step claims.
- New nodes: none; the item itself is the only node file, and no auxiliary statement was introduced.
- Form and searches: statement is self-contained, uses no undefined project notion, and records the LeanFinder, Loogle, grep, and unavailable LeanSearch runs in `searches.jsonl`; the blueprint provenance and Mathlib declaration, file, line, and specialization are recorded in the node. Verdict: pass.
- Edge cases: checked `p = p'` (the returned prime may be the starting prime), a field/zero-prime situation, and the zero ring/empty spectrum situation; all are either vacuous or covered by the stated prime hypotheses. Verdict: no statement change needed.

Changes made: none to the mathematical statement or node set; this second-reading audit adds the source comparison, specialization check, search/form checks, and edge-case checks required before delivery.
