# Delivery report: lem-exc-residue-tor-test

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-residue-tor-test.json`: existing statement node retained and marked `split`; no new nodes or Mathlib leaves.
- `citations.json`: 14 verbatim citation entries, one for every cited node in the six proof steps.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, residue-Tor names, and likely declaration names; no declaration with the blueprint tag or an exact sorry-free statement exists.

## WANTED

None.

## What was checked and corrected

The imported statement had already been repaired to make the coefficient extension (E/\mathbf Q_\ell), valuation ring, uniformizer, positive level (n\), residue field, scheme, ordinary small-etale derived category, bounded constructibility, and integer endpoints explicit. I retained those hypotheses and the exact interval. The earlier blueprint prose used pro-etale-only tensor/Tor terminology for an etale object; the node's statement and proof consistently use the existing ordinary-etale definitions. No target statement was weakened.

The current main-20261015 blueprint item and proof were read, as was the imported node's source and all cited node statements. The proof has no newly introduced auxiliary node: each step is a complete argument and the cited facts are strictly smaller existing nodes.

## Review by Q64

1. I read the coefficient-ring sources and the statements of `lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients`, `def-weil-pbc-constant-sheaf`, and `lem-weil-pbc-site-module-presheaf-sheafification-exact`. Step 1 uses exactly their conclusions: the valuation ring is a DVR with finite residue field, its finite quotient is local, constant sheaves are sheafifications, and sheafification is exact. This verifies that (A=\mathcal O_E/\varpi_E^n), (\kappa=A/(\varpi_E)), and the induced (\kappa_T)-action are well-defined.
2. I checked `def-kun-tor-amplitude`; step 2 is its forward implication with the degree-zero module (\kappa_T), so no additional hypothesis is used.
3. I read `lem-pc-kflat-resolution` and `def-kun-derived-tensor`. Step 3 uses their stated K-flat resolution and the fact that tensoring that resolution represents derived tensor for arbitrary module sheaves; it does not assume the resolution is bounded.
4. I read `lem-pc-sites-module-sheafification-tensor`, `lem-weil-pbc-site-module-presheaf-sheafification-exact`, and `def-pur-sheaf-tensor-product`. Step 4 first performs the sectionwise vector-space calculation over the field (\kappa), then uses precisely the cited sheafification/tensor identifications and the explicit balanced maps to obtain the complex isomorphism ((P\otimes_{A_T}\kappa_T)\otimes_{\kappa_T}N\cong P\otimes_{A_T}N). The argument is natural in restrictions and does not treat sections of (\kappa_T) as a field.
5. Step 5 is elementary: the images (F_sM=\operatorname{im}(\varpi_E^s)) form a finite filtration, (F_nM=0), and each quotient is killed by (\varpi_E). I checked this for arbitrary sheaves, including nonconstructible ones.
6. I read `def-pc-flat-sheaf-modules`, `lem-weil-pbc-complex-ses-homology-long-exact`, `def-kun-derived-tensor`, and `def-kun-tor-amplitude`. Step 6 applies flatness termwise to each short exact filtration sequence, uses the cited long exact sequence, and performs the finite descending induction from (F_nM=0). It then translates the resulting cohomology vanishing back to derived tensor and the definition of Tor amplitude.

I tested edge cases in the statement and argument: (n=1) makes the filtration a single residue-field layer; the zero complex is immediate; an interval with no nonzero cohomology is handled by the same vanishing argument; and the proof never assumes finite generation of the arbitrary test sheaf (M). The dependency union equals `proof_deps`, and no new node or cycle was introduced.

## What could not be finished

Nothing remains for this stage-1 split.
