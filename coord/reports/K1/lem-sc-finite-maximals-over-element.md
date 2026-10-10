Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-finite-maximals-over-element.json` (statement, split; no Mathlib match)
- `dag/nodes/sec-curve-estimates/lem-sc-finite-minimal-primes-over-ideal.json` (statement, Mathlib leaf: `Ideal.finite_minimalPrimes_of_isNoetherianRing`)
- `citations.json`

Attachments: none.

WANTED: `literature/stacks-project/algebra.tex`, Lemma Tag 00PF, because the project checkout has only the citation index; the cited Stacks text was read from `/home/ubuntu/c1-stacks-review/algebra.tex`.

## Not duplicates

`lem-sc-finite-minimal-primes-over-ideal` vs `lem-weil-pbc-noetherian-finitely-many-minimal-primes`: the new node concerns minimal primes over an arbitrary ideal I, while the existing node only concerns minimal primes over the zero ideal.

`lem-sc-finite-minimal-primes-over-ideal` vs `lem-weil-pbc-popescu-reduce-to-field`: the existing 00FR-tagged node is a Popescu reduction theorem whose statement does not assert finiteness of minimal primes over an ideal; the new node is the finite-minimal-primes theorem.

`lem-sc-finite-minimal-primes-over-ideal` vs `lem-weil-pbc-reduced-noetherian-total-ring-fractions`: the existing 00FR-tagged node decomposes the total ring of fractions using the already finite set of minimal primes of a reduced ring; it does not state finiteness of minimal primes over an arbitrary ideal.

`lem-sc-finite-maximals-over-element` vs `lem-sc-finite-length-global-submodule`: this item only proves finiteness of maximal ideals containing x; the global finite-length node additionally proves finite length of M/xM for every fraction-field submodule M.

## Review by K1

I read the Tag 00PF proof at `/home/ubuntu/c1-stacks-review/algebra.tex` lines 29266-29290. Its opening argument says that in a Noetherian one-dimensional domain a nonzero x lies in finitely many primes, each maximal; the item statement is exactly that support assertion with the same hypotheses. I also read the existing DAG node `lem-weil-pbc-prime-contains-minimal-prime`: it supplies a minimal prime over xR below any prime containing x, exactly as used in step 2. The new node is the arbitrary-ideal strengthening of the existing zero-ideal finite-minimal-primes node, so it is not a duplicate; its Mathlib declaration was checked in `Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean`.

Step 1 uses only the new node's statement: minimal primes over I=xR form a finite set. Step 2 uses the cited prime-containment statement to choose p below each maximal m and the Krull-dimension definition to rule out a strict chain 0 < p < m. The domain hypothesis and x nonzero ensure p is nonzero, so p=m; this identifies the desired maximal ideals with a subset of the finite minimal-prime set. The dimension argument is elementary once the definition and cited containment lemma are in hand. I checked the unit case (the set is empty), R=Z with x=2 (only (2)), and a general field (no nonzero proper maximal-containing element) for the edge behavior.

The required LeanFinder, Loogle, and Mathlib grep searches were run for the item and for the new leaf; the exact Mathlib match is recorded in the leaf, while the grep query itself returned no hit. The item has no sorry-free project declaration tagged with this blueprint id, so it required a split.

## Second reading by K1

- Item statement: checked against Algebra Tag 00PF, label `lemma-finite-length-global`, lines 29266-29290; the Noetherian domain, dimension-one, nonzero-element hypotheses and finiteness of maximal ideals containing the element agree with the source's finite-prime support assertion (each such prime is maximal).
- Step 1: checked against the statement of `lem-sc-finite-minimal-primes-over-ideal`; it supplies exactly the finite set of primes minimal over $xR$, with $I=xR$.
- Step 2: checked against `lem-weil-pbc-prime-contains-minimal-prime` and the full Krull-dimension definition; containment of $x$ makes the chosen minimal prime nonzero in a domain, and a strict chain $0\subsetneq p\subsetneq m$ would have length $2$, contradicting dimension $1$. This is the only elementary deduction.
- `lem-sc-finite-minimal-primes-over-ideal`: checked against Algebra Tag 00FR, label `lemma-Noetherian-irreducible-components`, lines 6135-6150, after applying the finite-minimal-primes result to $\operatorname{Spec}(R/I)$; the statement is self-contained, uses the Noetherian definition node, is statement-only, and is an exact Mathlib leaf at `Ideal.finite_minimalPrimes_of_isNoetherianRing` (line 26).
- Blueprint and duplicate checks: searched the DAG and imported blueprint for the two identifiers and the key phrases; no duplicate or blueprint node states finiteness over an arbitrary ideal. The existing zero-ideal finiteness node is strictly weaker.
- Edge cases: for a field and nonzero $x$, the set is empty; for $R=\mathbb Z$, $x=2$, it is the singleton $(2)$; for a unit $x$, it is empty. The hypotheses exclude the zero element, where the assertion would generally fail.
- Changes: corrected both `created.item` fields to this item, converted both new statements to the required TeX form, and made `citations.json` quote the repaired statements verbatim (including the full dimension definition).
