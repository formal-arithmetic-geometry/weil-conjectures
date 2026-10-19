# Stage-1 report: lem-trf-monoid-completion-coefficients

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-pattern-factorization.json` — statement-only auxiliary lemma; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-monoid-completion-coefficients.json` — repaired item split; no exact Mathlib match.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none. No finished declaration with this statement was found in `WeilConjectures/` of either source checkout.

WANTED: none.

The returned version had stale `created.item` and `created.group` metadata, which now identify this item and NH. Its Step 5 claimed the reverse inclusion of the kernel equality by an unproved finite partition. I added `lem-trf-finite-pattern-factorization` as the precise auxiliary statement and rewrote Step 5 to construct the partition: the finite low-`nu` set is handled term by term using maximal-ideal generators and chosen decompositions, while the high-`nu` indices are assigned to finitely many generator prefixes and factored as prefix monomials times residual families. I searched the whole DAG and blueprint before adding the auxiliary node; no node states this arbitrary positive-monoid coefficient factorization.

## Not duplicates

- `lem-trf-finite-pattern-factorization` vs `lem-trf-completed-monoid-support-projection`: the new lemma gives ideal-power factorization for arbitrary finitely generated positive monoids and mixed maximal-ideal/monomial generators; the existing node concerns a lattice intersection monoid embedded in an orthant and a supported-series retraction, with no ideal-power factorization.
- `lem-trf-finite-pattern-factorization` vs `lem-weil-pbc-power-series-combined-ideal-coefficients`: the new lemma is for arbitrary embedded positive monoids and convolution families in an adic completion; the existing node is the coefficient criterion for ordinary multivariate power series.

## Review by NH

I reread the item, its chapter and unit records, the returned review entry, ILO VI 1.6(i)--(ii), and Stacks Tag 05GG. I also reread the existing completed-monoid support node and the combined-ideal power-series coefficient node before deciding that neither states the needed factorization. The new auxiliary node's statement exactly supplies the reverse-inclusion claim used in Step 5 and has its own recorded searches.

For Step 1 I checked the positive-weight bound, attainment of `nu`, finiteness of `{p: nu(p)<n}`, and finiteness of decompositions contributing to a convolution coefficient. Step 2 checks both directions of the finite-level coefficient criterion, including `p=0` and `nu(p) >= n`. Step 3 uses only the inverse-limit completion and complete/separated coefficient-ring definitions to construct the coefficient family and its inverse. Step 4 checks coefficientwise addition, finite convolution multiplication, and monomial images.

I repaired Step 5 in detail. The finite low-`nu` set is treated individually; finite generation of `m` expands each coefficient into finitely many products, and a chosen maximal decomposition supplies the monomial factors. For the high-`nu` part, each element has an `n`-term nonzero decomposition; choosing one generator from a generator word for each summand leaves a residual element of `P`, and only finitely many generator-prefix tuples occur. Assigning each index to the first eligible tuple makes each class a prefix monomial times one residual family, so the finite sum lies in `b^nB`. This verifies the exact conclusion of the new cited node and closes the kernel equality. Step 6 then reads off the finite direct-sum quotient from the repaired kernel criterion and Step 1. Edge cases `P={0}`, `n=1`, and `P=N` remain valid. No SGA source is cited, and no proof step exceeds the 2000-character review threshold.
