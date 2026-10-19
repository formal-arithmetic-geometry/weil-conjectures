# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/det-uniform-constructible-ext-integral.json`: six-step split of the imported statement; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim excerpts for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, the key notions, and the blueprint tag; no sorry-free declaration states this item.

## WANTED:

None.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report. The existing nodes cited by the split were checked against the whole DAG before retaining them.

## What was wrong or incomplete in the imported split

The imported proof did not expose the integral coefficient comparison in enough detail and left the passage from derived global sections to a derived inverse limit without a DAG citation. I expanded the proof into six steps: integral lattice reductions and completion; limit preservation by support and tensor functors; the support-Hom formula and derived sections; coefficient-change adjunction for finite reductions; application of the torsion bound in its finite coefficient category; and the Milnor degree shift. I reused the existing statements for integral models, derived completion, closed support, coefficient change, the torsion bound, derived global sections, and the Milnor sequence. No new node was needed.

## Review by N3

I read the target source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-integral.md`, the complete route in `sk-lem-uniform-constructible-ext/_section.md`, and the chapter route. I checked that the target keeps the torsion situation's locally closed source and target factorizations, lattices, uniformizer, coefficient category, and cohomological-dimension hypotheses exactly, with Ext in the integral pro-étale derived category.

For step 1 I opened `sk-lem-integral-models.json` and verified that clause 4 supplies the extensions by zero, their derived reductions, and derived completeness in the integral setting. I opened `sk-def-pe-derived-completion.json` and checked that its canonical map is precisely the inverse-limit criterion used. The step introduces the restriction of scalars for finite reductions explicitly and adds no flatness hypothesis.

For step 2 I opened `sk-lem-formal-closed-support-ii.json`; its statement says that support, open pullback, and tensoring with a finite locally free module commute with sequential derived limits. This is exactly the assertion used to reconstruct `F` from `F_n`; the finite locally free dual is constructed locally and glued by inverse-transpose transition matrices.

For step 3 I opened `sk-lem-formal-closed-support.json` and checked its second clause gives the displayed support-Hom formula. I also checked `lem-kun-site-rgamma-derived-limit.json`, whose statement gives the derived-global-sections comparison for a tower on a ringed site with terminal object. These two statements justify the identification of the integral Ext complex with the derived limit of the `B_n`.

For step 4 I opened `sk-def-sfb-coefficient-change.json` and verified that derived extension of scalars is left adjoint to restriction for an arbitrary coefficient morphism. I checked clause 4 of `sk-lem-integral-models.json` for the source reduction. Thus the comparison is between the integral and finite coefficient module categories and does not identify those categories or assume flatness.

For step 5 I opened `sk-lem-formal-closed-support.json` and `det-uniform-constructible-ext-torsion.json`. The former supplies the finite-coefficient support-Hom expression; the latter's clause 2 states vanishing above `cd_ell(j)+cd_ell(S)+1` for exactly the reduced objects. I checked that the dual reduction is identified locally by the finite-basis evaluation pairing and that the finite ring is killed by a power of `ell`, so the torsion theorem is applied in its own coefficient category.

For step 6 I opened `lem-pc-derived-limit-milnor-sequence.json` and verified its short exact sequence with both `lim` and `R^1 lim`. Applying it to the tower from step 3 makes both end terms vanish when `q>c+1`, where `c=cd_ell(j)+cd_ell(S)+1`; this gives the claimed `+2` bound. No surjectivity or Mittag-Leffler assumption is used. I tested the zero tower and the case of zero cohomological dimensions symbolically; both agree with the stated shift.

I checked every quote in `citations.json` verbatim against its cited node statement. The server `check_dag` and `review_split` checks passed, and the delivery preflight dry run passed.

## Second reading by N3

- Item statement: checked against the blueprint node and its Stacks cross references (Tags 09BP, 09BM, and 08TB); the locally closed factorizations, integral lattices, coefficient category, and strict `+2` bound agree hypothesis by hypothesis.
- Step 1: checked [sk-lem-integral-models] clauses (2)--(4) and [sk-def-pe-derived-completion] against the integral-models paragraph; the reductions, restriction of scalars, and derived-completeness conclusion are stated by those nodes, with no extra flatness assumption.
- Step 2: checked [sk-lem-formal-closed-support-ii] against the limit-preservation paragraph; its hypotheses cover the support pullback and finite locally free tensor functors, and the local dual construction supplies the finite locally free tensor factor used here.
- Step 3: checked [sk-lem-formal-closed-support] clause (2) and [lem-kun-site-rgamma-derived-limit] against the support-Hom and derived-sections paragraphs; both cited statements give exactly the displayed identifications and the passage of the sequential derived limit through global sections.
- Step 4: checked [sk-def-sfb-coefficient-change] and [sk-lem-integral-models] clause (4) against the finite-coefficient comparison paragraph; the adjunction compares the two module categories and does not require flatness.
- Step 5: checked [sk-lem-formal-closed-support] clause (2) and [det-uniform-constructible-ext-torsion] clause (2) against the torsion reduction display; the finite ring, dual reduction, and uniform vanishing range match the cited hypotheses.
- Step 6: checked [lem-pc-derived-limit-milnor-sequence] against `more-algebra.tex`, Tag 07KY, label `lemma-break-long-exact-sequence`, and the product description in `derived.tex`, Tag 08TB, label `section-derived-limit`; the index shift gives vanishing for `q>c+1`, hence the claimed `+2`, with no Mittag--Leffler assumption.
- New nodes: none; therefore B1--B7, duplicate searches, and Mathlib-leaf checks are vacuous. Existing dependency statements were read in the shared DAG and all citation quotes remain verbatim in `citations.json`.
- Source hypotheses: read `proetale.tex`, Tag 09BP, label `lemma-j-shriek-limits` (quasi-compact open immersion), and Tag 09BM, label `lemma-closed-immersion-complement-retrocompact-exact` (retrocompact complement); both hypotheses hold for the Noetherian standing schemes used by [sk-lem-integral-models]. Read `sites-cohomology.tex`, Tag 0D6K, label `lemma-RGamma-commutes-with-Rlim`, for Step 3; it applies to the stated ringed site without a boundedness hypothesis on the tower.
- Edge cases: if either lattice is zero, every relevant Ext group and the corresponding tower are zero; if the source or target stratum is empty, the extension by zero is zero; for `n=1` the finite coefficient ring is the residue field and the same adjunction and bound apply. `n=0` is outside the statement's `n>=1` range. For an algebraically closed base field and identity strata, both cohomological dimensions are zero and the asserted bound is the (possibly nonsharp) bound `q>2`; the Milnor calculation gives exactly that range. Infinite cohomological dimension makes the asserted range empty.
- Independent search: ran LeanFinder through `msearch.py` with “Ext groups of integral local systems vanish above a uniform cohomological dimension after reduction to finite torsion coefficients”; all eight returned declarations concern abstract injective/projective dimension or a projective object's Ext vanishing, and none supplies the stratum bound or its hypotheses. The actual response is recorded in `searches.jsonl`.
- Changes: appended this second-reading record and the independent search log only; no mathematical or node-file changes were necessary.
- Validation: the mandated delivery-tool dry run completed with `OK (not pushed)` at `a83aebb977`; server preflight passed. The installed tool accepts `--no-push` without the brief's trailing dot, so that supported invocation was used.
