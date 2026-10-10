1. files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-plus-locally-free.json`: split item, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-pseudo-coherent-lift.json`: statement node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-truncation-kernel-finite-locally-free.json`: statement node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-perfect-ext-bounded-qcoh-vanishing.json`: statement node, no Mathlib match.

2. attachments: none.

3. WANTED: none.

4. The item was unsplit and has no exact declaration in either Lean checkout. I read the complete proof of Stacks Tag 08ED in `/home/ubuntu/c1-stacks-review/perfect.tex` (the repository's literature checkout is metadata-only). The first step uses the existing perfect-implies-pseudo-coherent-and-locally-finite-Tor statement and the new Tag 08EE lifting statement. The second step uses the new truncation-kernel statement, whose hypotheses match the chosen lower Tor bound and whose conclusion is exactly the finite locally free sheaf used in the truncation triangle. The third step uses the new Tag 09M4 vanishing statement; its affine scheme is quasi-compact and quasi-separated, and the shifted kernel complex is bounded and quasi-coherent. The fourth step is the elementary split-triangle argument from the source. I checked the zero complex and rank-zero summand cases: taking the zero finite-free complex gives the expected zero summand, and the split triangle remains valid.

5. Nothing remains unfinished. Mathlib searches were run for each new statement with LeanFinder, Loogle, and Mathlib grep; all found no matching theorem.

## Review by J1

I checked the item's statement against Tag 08ED and retained its hypotheses and conclusion. I read each new node's source passage in `perfect.tex`, verified that the statements introduce all objects they use, and searched the entire DAG for the Stacks tags and key phrases before creating them. Step 1 cites exactly the existing perfect Tor/pseudo-coherence statement and the new lifting statement. Step 2 cites exactly the truncation-kernel conclusion; the affine and Tor-amplitude hypotheses are supplied by the preceding steps. Step 3 cites exactly the interval-vanishing Hom conclusion and verifies that the shifted kernel is a bounded quasi-coherent target. Step 4 uses only the standard split-triangle argument and the finite-free definition of perfectness. The citations file quotes verbatim clauses from every cited node. I corrected the imported item's empty proof and metadata by adding these four source-faithful steps and the three necessary statement-only auxiliaries.

## Not duplicates

lem-sc-affine-truncation-kernel-finite-locally-free vs lem-sc-affine-perfect-plus-locally-free: the new node is the lower-truncation kernel lemma for a chosen bounded-above finite-free representative and a Tor-amplitude bound; the existing item asserts existence of a finite locally free summand and an affine perfect extension for every perfect object.

## Second reading by J1

- Item statement: checked against Stacks Tag 08ED (label `lemma-lift-perfect-complex-plus-locally-free`) hypothesis by hypothesis; verdict: agrees.
- Step 1: checked the pseudo-coherence/finite-Tor statement and Tag 08EE lifting statement; verdict: cited conclusions supply the bounded-above finite-free lift.
- Step 2: checked Tag 08ED's truncation and displayed triangle; verdict: corrected the kernel claim to flatness and finite presentation only after restriction to U, and made the sheaf and shifts explicit.
- Step 3: checked Tag 09M4 (label `lemma-ext-from-perfect-into-bounded-QCoh`) and the bounded one-sheaf shift; verdict: the chosen negative shift lies outside the vanishing interval, so the connecting morphism is zero.
- Step 4: checked the split-triangle argument cited by Tag 08ED; verdict: the right-inverse/direct-sum argument is written explicitly and the finite locally free summand is identified correctly.
- `lem-sc-affine-pseudo-coherent-lift`: checked against Tag 08EE; verdict: self-contained statement-only auxiliary, no existing DAG or Mathlib match.
- `lem-sc-affine-truncation-kernel-finite-locally-free`: checked against Tag 08ED; verdict: repaired false affine-flatness assertion and added the missing Tor-amplitude and finite-locally-free dependencies.
- `lem-sc-perfect-ext-bounded-qcoh-vanishing`: checked against Tag 09M4; verdict: statement matches clause (1), with all objects introduced.

Changes made: corrected the item's `created.item` identifier, replaced the false claim that K is flat over A by the source's restricted flatness claim, updated the citation quote, and clarified the truncation shifts and split-triangle conclusion. Zero-complex and rank-zero cases remain consistent.
