# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-embedded-points-affine-removal.json`: split statement, four proof steps, Mathlib searches recorded.
- `dag/nodes/sec-abelian-varieties/lem-sc-hilbert-finite-submodule-noetherian.json`: Mathlib leaf, `isNoetherian_of_isNoetherianRing_of_finite` plus `IsNoetherian.noetherian`.
- `citations.json`: seven verbatim step-to-node quotes.

2. Attachments: none.

3. WANTED: none; the local Stacks source `/home/ubuntu/c1-stacks-review/algebra.tex` contains Tag 02M6.

4. The item had no Lean declaration and no duplicate blueprint/DAG node. Its stale unsplit state was expanded following Tag 02M6. The only new subordinate fact is finite generation of a submodule of a finite module over a Noetherian ring; Mathlib states this through its Noetherian module theorem, so it is recorded as a leaf. The existing associated-prime finiteness, minimal-support association, and submodule-inheritance nodes were reused.

## Review by M1

I read the item, its chapter/unit records, the parent node `lem-sc-hilbert-embedded-points`, and the exact Tag 02M6 source in `algebra.tex` (lines 16468 onward). I also searched the Lean source for the blueprint tag and the relevant Hilbert/embedded-prime terminology; no project declaration proves this item. The four steps follow the source: finite decomposition of associated primes and minimal support primes; construction and finiteness of K; maximality using localization at minimal support primes and associated-prime inheritance; and the quotient, no-embedded-prime, support, and localization conclusions.

For each citation I opened the cited node and checked that its statement supplies the precise fact used. Step 1 uses finiteness of `Ass(M)` and that minimal support primes are associated. Step 2 uses the new Mathlib leaf's exact finite-submodule conclusion. Step 3 uses the existing submodule associated-prime inclusion, finiteness, and minimal-support result. Step 4 uses the minimal-support associated-prime statement for the quotient argument. I verified the hypotheses R Noetherian and M finite are present throughout, and checked boundary cases: if there are no embedded primes then K is zero; localization at an element in every embedded prime kills K. The Mathlib searches included LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such in the command log, while the other searches found the finite-submodule theorem.

5. Nothing remains unfinished. The required dry run is the final check.

## Not duplicates

lem-sc-hilbert-finite-submodule-noetherian vs lem-sc-hilbert-embedded-points-affine-removal: the new node states only finite generation of an arbitrary submodule of a finite Noetherian module, while the item constructs a maximal nowhere-dense submodule and proves quotient support, associated-prime, and localization conclusions; Tag 02M6 is the source context for both but the statements are not equivalent.

## Second reading by M1

- Item statement: checked against Tag 02M6, Definition `definition-embedded-primes`, and the localization definition; verdict: correct after making support and embedded-prime meanings explicit.
- Step 1: checked against Tag 02M6 first paragraph and nodes `lem-weil-pbc-noetherian-associated-primes-finite`, `lem-weil-pbc-minimal-support-prime-associated`, and `def-weil-pbc-module-localization`; verdict: correct, with the localization nonvanishing argument written out.
- Step 2: checked against Tag 02M6 construction of K and the Mathlib finite-submodule leaf; verdict: elementary closure/support argument and nowhere-dense conclusion now stated explicitly.
- Step 3: checked against Tag 02M6 maximality paragraph and the associated-prime submodule and minimal-support nodes; verdict: corrected the omitted minimal-prime-in-the-cyclic-support argument.
- Step 4: checked against Tag 02M6 quotient and localization paragraphs and the minimal-support/localization definitions; verdict: support equality, absence of embedded primes, and localization isomorphism are stated with their intermediate implications.
- New node `lem-sc-hilbert-finite-submodule-noetherian`: checked as a strict auxiliary fact and against Mathlib declaration `isNoetherian_of_isNoetherianRing_of_finite`; verdict: valid Mathlib leaf, with recorded searches and line.
- Changes: added self-contained support and embedded-prime definitions and the localization dependency; expanded Steps 1, 2, 3, and 4; added matching citations and this second-reading record.
