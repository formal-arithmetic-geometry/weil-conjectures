# Lead review: `lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence`

## Source search

I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id,
the `(blueprint: ...)` tag, and the notions `relative global complete
intersection`, localization at a prime, and regular sequence.  There is no
declaration with this statement and no matching blueprint-tagged declaration.
The regular-sequence files found there provide only general transport and
local-ring infrastructure; none states the relative complete-intersection
claim.  Thus this item is a split rather than a Lean attachment.

## Review by K1

The source is Stacks Algebra, Lemma 00SV
(`lemma-relative-global-complete-intersection-conormal`), assertion (1).
The item statement is exactly assertion (1): for a relative global complete
intersection presentation and a prime of its quotient, the defining
polynomials form a regular sequence in the corresponding localized
polynomial ring.  The split report identifies the nearest blueprint ancestor
(`thm-weil-pbc-finite-etale-lifting`, proof step 7) and has `same_as: []`;
the item has the required `blueprint` and `split_report.blueprint` fields.

### Steps

1. In the Noetherian case, step 1 sets
   `p = R ∩ q'` and `B = P_q'`, and cites the polynomial-ring basis,
   projective-module flatness, finite-type Noetherianity, flat local ring map,
   and the localization description of the closed fibre.  These cited
   statements supply each assertion used; the step is not elementary.
2. Step 2 identifies the fibre with `k[x_1,...,x_n]` using polynomial scalar
   extension, transports the prime using the fibre-prime bijection, and
   applies relative-GCI base change and the global-GCI regular-sequence lemma
   (00SC) to obtain regularity in the fibre.  The cited fibre local-ring
   isomorphism carries the classes back to `B / pB`.  Each cited node states
   the claimed transport or identification; no proof body of a node is used.
3. Step 3 applies the cited Grothendieck regular-sequence lemma (00MG) to
   the flat local map from step 1 and the fibre regular sequence from step 2.
   It also checks the empty-sequence case through the nonzero localization at
   a prime.  This step is not elementary.
4. For arbitrary `R`, step 4 uses the cited Noetherian-approximation and
   base-change statements to form finite-type `Z`-subalgebras and their
   induced primes.  It follows the approximation paragraph of 00SV,
   lines 36794--36807; all invoked facts are cited.
5. Step 5 explicitly identifies the localized rings and their quotients as a
   filtered colimit.  The finite-coefficient argument establishes both
   surjectivity onto the localization and eventual vanishing of a zero
   fraction, and the same argument gives the quotient identifications.  This
   is the colimit argument in 00SV, lines 36808--36815 and 36818--36828;
   the localization definition is the only cited non-elementary fact.
6. Step 6 applies exactness of filtered colimits to the compatible
   multiplication maps, proving injectivity on every successive quotient,
   and identifies the final quotient with the nonzero localization `S_q`.
   Together with the cited regular-sequence definition this gives the
   conclusion.  The exactness assertion is cited; the remaining quotient
   check is a direct localization calculation.

### Split and mathematics checks

The split has no new nodes, so B1--B8 (self-contained statements, TeX,
source labels, and Mathlib-leaf requirements) introduce no additional leaf
review.  The existing dependencies were searched before accepting the split;
`python3 tools/review_split.py` reports `PASS; 0 new nodes`.  The source
statement and all six steps agree with 00SV assertion (1) and its proof at
lines 36783--36831.  Hypotheses checked include Noetherianity and flatness in
step 1, nonzero fibre and dimension `n-c` in step 2, local Noetherian rings
and fibre regularity in step 3, finite-type approximation and base change in
step 4, localization/filtered-colimit identities in step 5, and injectivity
plus nonzero final quotient in step 6.  Small edge cases `c=0` and a prime
localization are explicitly handled in step 3 and step 6.  No false source
claim or missing hypothesis was found, and no repair was sent to the worker.
