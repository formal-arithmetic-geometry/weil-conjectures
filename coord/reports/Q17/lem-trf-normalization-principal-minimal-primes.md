# Stage 1 report: lem-trf-normalization-principal-minimal-primes

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normalization-principal-minimal-primes.json`: split item; six proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-normalization-integral-closure-krull.json`: new statement-only unsplit node, Mori–Nagata for normalization in the base's own fraction field; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-krull-principal-primary-decomposition.json`: new statement-only unsplit node, the height-one localization components and their radicals for a principal ideal of any Krull domain; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each node used by each step.

## Attachments

None. Project-source searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, normalization/minimal primes, Krull domains, Mori–Nagata and principal primary decomposition found no exact declaration. Related Noetherian-minimal-prime and Dedekind-domain declarations do not prove this item.

## WANTED

WANTED: `literature/swanson-huneke-integral-closure.pdf`, Definition 4.10.1 and Proposition 4.10.3 (printed p. 89), Theorem 4.10.5 (printed pp. 90–91), and Proposition 4.8.2 proof (printed p. 84), for this item and the two new nodes. The local PDF is absent. I read the author-hosted PDF at https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf without downloading a new local literature file. The item's proof is marked `by: agent`: its reduction and final calculation are written out, and the two textbook inputs are separate statement-only nodes.

## What was wrong or changed

The imported item had no proof. Its statement is correct and unchanged, including the absence of any finite-module or Noetherian-ring hypothesis on the normalization D. I corrected the source place: Proposition 4.8.5 is a residue-field theorem; the needed finite-extension reduction is in the proof of Proposition 4.8.2. Proposition 4.10.3 is on printed p. 89, not p. 90.

The six-step proof carries the finite-extension reduction rather than putting it into a new lemma: choose a field basis, write monic equations by linear dependence, scale their coefficients by explicit denominators, and take the resulting finite integral algebra S. Existing nodes give S's module finiteness, integrality and Noetherianity. Its fraction field is F by the basis calculation. Integral transitivity identifies the normalization of S in F with D. The first new node is then the exact own-fraction-field Mori–Nagata theorem. The second new node is the independent principal-primary decomposition theorem for any Krull domain. Its statement gives the actual ideals J_i and their radicals; the item's last step proves the desired finite radical equality by choosing a maximum of the finitely many exponents. Thus the new nodes are structural inputs, and the item proves its finite-extension reduction and conclusion explicitly.

No target, unit or chapter statement was changed. The historical ancestry through `lem-trf-local-term-locality` and the parent Heinzer induction is retained. No SGA source is used.

## Not duplicates

- `lem-trf-normalization-integral-closure-krull` vs `lem-trf-normalization-principal-minimal-primes`: the new node is the own-fraction-field Mori–Nagata structure theorem (height-one local normal Noetherianity, intersection, and finite character), not the item’s finite-extension principal-radical conclusion.
- `lem-trf-normalization-integral-closure-krull` vs `lem-trf-integral-extension-noetherian-spectrum`: the existing parent proves topological Noetherianity by induction and uses the item. The new node proves Krull structure in the own-fraction-field case; it cites neither the parent nor the item, so there is no cycle.
- `lem-trf-normalization-integral-closure-krull` vs `lem-sc-integral-closure-dedekind-surjective-fibres`: the existing node assumes a one-dimensional base and proves Dedekindness and finite fibres. Mori–Nagata has no dimension bound and asserts Krull structure.
- `lem-trf-krull-principal-primary-decomposition` vs `lem-trf-normalization-principal-minimal-primes`: the new theorem concerns any Krull domain and identifies the actual primary components J_i = D intersect bD_{P_i} and their radicals. The item concerns finite-extension normalizations and derives a radical-only decomposition from it.
- `lem-trf-krull-principal-primary-decomposition` vs `lem-trf-ufd-height-one`: the latter is a UFD criterion, assumes the ring Noetherian and has no primary-decomposition assertion.

Whole-DAG searches for Krull domains, Mori–Nagata, the textbook places and principal primary decomposition, plus whole-blueprint searches for these notions, found no equivalent node. The remaining primary-decomposition hits are finite-group or constructible-sheaf primary decompositions, not ring-ideal decompositions.

## Review by Q17

I read delivery-errors B through E and checked the final files against them. I read the item, its parent `lem-trf-integral-extension-noetherian-spectrum`, the `sk-i-curve-zero` unit and chapter record, the current ancestor route, and the online author-hosted Swanson–Huneke pages named above. I checked Definition 4.10.1 against the exact three Krull properties in both new nodes. Theorem 4.10.5 is used for a Noetherian domain in its own fraction field, so the new statement does not silently assume finite normalization or separability. Proposition 4.10.3 states the principal ideal is the intersection of its height-one localization contractions as a primary decomposition; these components have the corresponding primes as radicals, exactly as the second new node states.

Step 1 is elementary finite-dimensional linear dependence and an explicit scaling of the monic relation: d_i^(n_i-j)c_ij lies in R because d_i c_ij does. Step 2 uses the exact statements of `lem-weil-pbc-finite-of-integral-generators`, `lem-weil-pbc-finite-algebra-is-integral` and `lem-weil-pbc-finite-type-algebra-noetherian`, all read in full. They apply to S, whose displayed generators are integral and whose base R is Noetherian. The fraction-field equality is proved from the finite basis, without assuming the basis elements integral before scaling. Step 3 cites the finite-generation and finite-integrality nodes again to make S[x] integral over S, so the ring-map version of `lem-weil-pbc-integral-transitive` truly applies; it is not incorrectly used as an elementwise theorem without checking S[x]. The two inclusions of integral closures are written explicitly. Step 4 applies the new Mori–Nagata statement to S with fraction field F established in Step 2; Step 5 uses the new principal-primary theorem at D, known Krull by Step 4. Step 6 is the written finite-exponent argument and handles the empty list. Every cited sentence appears verbatim in `citations.json`; no definition node substitutes for a theorem. All off-unit proof tools are existing Mathlib leaves, and both new nodes inherit this unit.

I tested the statements at a field and at a DVR, at k[x,y] (Krull of dimension two, so Dedekind hypotheses cannot be substituted), with b a unit in a nonfield domain, with b nonunit, in the degree-one extension, and in an inseparable finite extension. The field/unit case has t=0 and bD=D. The construction of S and the Mori–Nagata use do not require separability. The hypothesis b nonzero is retained. The final new statements are self-contained and contain no proof sketches; all proof steps are under 2000 characters.

Mathlib searches were run through msearch and recorded from the log with their exact query text. Each new statement has LeanFinder in two phrasings, Loogle, source grep and LeanSearch. I read the relevant returned sources: DedekindDomain/IntegralClosure.lean:145–175 assumes an integrally closed Noetherian base and separability, Ideal/MinimalPrime/Noetherian.lean:24–27 assumes the ring containing the ideal is Noetherian, and Lasker.lean:15–40 has the primary-decomposition interface only under its additional IsLasker hypothesis. DedekindDomain/Factorization.lean assumes IsDedekindDomain for its factorization results. None is the needed arbitrary-normalization or non-Noetherian Krull theorem. The initial Loogle query with an unknown KrullDomain identifier is explicitly inconclusive, not evidence of absence; the valid quoted-name Loogle searches also ran. No search that did not run was recorded.

The first server check found missing chapter fields on the new nodes; I fixed both chapter and unit metadata. During the mathematical self-review I replaced the initial overly compressed application proof with the final explicit six steps and replaced the prospective radical-only child with the actual primary-component theorem before delivery. The final report describes only the resulting three node files.

## What could not be finished

Nothing remains in this one-level stage-1 split. The two new structural lemmas remain unsplit as required; they join the future queue. No Lean code, compiler or build tool was used.
