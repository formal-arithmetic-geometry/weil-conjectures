1. Files written:
   - `dag/nodes/sec-abelian-varieties/lem-sc-ass-weakass-fg-prime.json`: statement, split proof, and Mathlib searches; status `split`.
   - `dag/nodes/sec-abelian-varieties/lem-sc-weakass-localization.json`: statement-only supporting node; no Mathlib match.
   - `dag/nodes/sec-abelian-varieties/lem-sc-associated-localization-fg.json`: Mathlib leaf for the associated-prime localization descent theorem.
   - `citations.json`: verbatim statement quotes for every cited proof step.
2. Attachments: none.
3. WANTED: `literature/stacks-project/algebra.tex` is not present in this checkout; Tag 058A and its supporting localization lemmas were read in the available Stacks source at `/home/ubuntu/c1-stacks-review/algebra.tex`.
4. The original item had no proof. I kept its statement and definitions, searched the whole DAG and blueprint for duplicate localization or weak-association nodes, and added only the two strict supporting facts needed by the source proof. The associated-prime support is a one-line specialization of Mathlib's localization theorem; weak association is not in Mathlib. The finite-generator argument is written in the item step rather than moved into a node that would restate the conclusion.

## Review by E1

I read Algebra Lemma 10.66.9 (Tag 058A) and its proof, including the cited localization lemmas 10.66.2 (Tag 0566) and 10.66.3 (Tag 0310). The item hypotheses match the source: a commutative ring, an R-module, and a finitely generated prime. Step 1 is the direct definition argument. Step 2 uses the new localization statement exactly for its clause that weak association gives an element of `M_p` with radical annihilator `p R_p`; the quote is recorded verbatim. Step 3 checks the finite list of generators, chooses minimal exponent sum, performs the exponent reduction, and verifies both inclusions of the annihilator. Step 4 uses exactly the Mathlib localization descent statement recorded in the supporting leaf, with the localized maximal ideal identified with `p R_p`.

For the new statement-only node I checked that its three clauses are precisely Tag 0566 and that no DAG or blueprint node already states them. Its four recorded searches ran; LeanSearch was unavailable and is recorded as such. For the Mathlib leaf I read `Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean`; the declaration `Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg` specializes to localization at `p` and the maximal ideal. I tested the item on the zero module (both predicates are false for a proper prime) and on a field with `p = (0)` and `M = R` (both predicates hold), so the equivalence does not introduce an existence claim.

## Not duplicates

`lem-sc-weakass-localization` vs existing weak-association nodes: existing nodes use the zero-divisor criterion or scheme-point specializations, whereas this node states the localization equivalence for arbitrary ring modules.
`lem-sc-associated-localization-fg` vs existing associated-prime nodes: existing nodes concern sheaf sections or different geometric hypotheses; this node is the ring-module localization descent specialization used by Tag 058A.
`lem-sc-associated-localization-fg` vs `lem-sc-ass-weakass-fg-prime`: the new node is only the localization-to-global associated-prime implication, while the item also includes weak association and the converse equivalence.
`lem-sc-associated-localization-fg` vs `lem-weil-pbc-associated-prime-localize-at-prime`: the existing node proves the opposite direction (global associated implies localized associated) for arbitrary rings; this node proves descent from localization under finite generation.
`lem-sc-associated-localization-fg` vs `lem-weil-pbc-noetherian-associated-prime-from-localization`: the existing node assumes the whole ring is Noetherian; this node assumes only that the one prime ideal is finitely generated, as required by Tag 058A.

## Second reading by E1

- Item statement: checked against Algebra Lemma 10.66.9, tag 058A (`lemma-ass-weakly-ass`), hypothesis by hypothesis; the commutative ring/module setting and finitely generated prime condition agree, and the two annihilator definitions reproduce `Ass` and `WeakAss`.
- Step 1: checked against the reverse implication in tag 058A; the direct definition argument is elementary and valid, including the zero module case.
- Step 2: checked against Algebra Lemma 10.66.2, tag 0566 (`lemma-weakly-ass-local`); the cited node supplies exactly the localized element with radical annihilator `p R_p`.
- Step 3: checked against the finite-generator exponent descent in tag 058A; the revised step explicitly minimizes the exponent sum and uses that `p R_p` is maximal to preserve the radical after replacing the element.
- Step 4: checked against Algebra Lemma 10.66.3, tag 0310 (`lemma-associated-primes-localize`); the supporting node states the required localization-to-global converse under finite generation.
- `lem-sc-weakass-localization`: statement-only form, self-contained localization hypotheses and definitions, source tag/label checked; searches were recorded and no Mathlib weak-association theorem was found.
- `lem-sc-associated-localization-fg`: statement-only form, source tag/label and localization hypotheses checked; the Mathlib declaration and source line are recorded, and it is a one-line specialization of the finite-generation converse.
- Small cases checked: the zero module gives no associated or weakly associated prime; for a field with `p = (0)` and `M = R`, both sides hold; the exponent argument also permits the zero prime generated by the empty list.

Changes made: repaired Step 3 to justify preservation of the radical annihilator during exponent descent, and added this second-reading audit. No node statements or citations required alteration.
