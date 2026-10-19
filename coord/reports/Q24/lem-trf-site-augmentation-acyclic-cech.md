## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-site-augmentation-acyclic-cech.json`: item, now split with three proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-site-augmentation-spectral-sequence.json`: new statement-only helper for the general arbitrary-site augmentation spectral sequence; no Mathlib match.
- `citations.json`: verbatim quotations for every cited node in every proof step.

Attachments: none. I searched the read-only slopmaster2 source for the item id, blueprint tag, and the augmentation/Cech concepts. No sorry-free declaration states this item. The prior Q118 dependency copy is unsplit and was used only as route context.

WANTED: none.

What was wrong or incomplete: the imported item had no proof and its general-site spectral-sequence input was not a DAG node. I added that input as a strictly more general, statement-only helper: it has no component-acyclicity hypothesis and only gives the E1 spectral sequence and canonical comparison. The item proof itself now handles the kernel identification, invokes the spectral sequence, and performs the vanishing-row collapse. No target statement or coefficient category was changed.

Nothing remains unfinished. The helper intentionally remains unsplit for the next stage.

## Review by Q24

I read the item and its source in `literature/stacks-project/spaces-simplicial.tex`, Tags 0D79 and 0D7A, including the double-complex construction and the degree-zero adjunction map. I also read the statements of every cited definition and the new helper. Step 1 is the vertex/edge argument: the augmentation adjunction identifies maps into `b_*F` with compatible component maps, and the two degree-one vertices force exactly the kernel of the first alternating differential; every pair of vertices in `[p]` is joined by an order-preserving `[1]` map, so the continuation is unique. This verifies that the resulting map is the stated mate `e`, including its degree-zero normalization. The hypotheses used are precisely the simplicial-object and geometric-morphism definitions.

Step 2 uses only the new helper's stated E1 spectral sequence and canonical comparison. I checked that its objects, slice topologies, component localizations, transition maps, and bounded derived category are all introduced in its own statement. Its source is the arbitrary-site Stacks 0D7A double-complex proof; the existing scheme-etale spectral-sequence node is not used because its coefficient and site hypotheses are narrower. The row-zero terms are exactly the displayed `C_b(F)^p` and the first differential is the stated alternating face sum.

Step 3 checks the actual hypothesis `R^q b_{p,*}F_p=0` for every `p` and `q>0`. It kills every positive row, so the first page is already the row-zero cohomology and the canonical comparison is a cohomology isomorphism in every degree. The derived-category criterion then gives the natural isomorphism, and the helper's q=0 edge together with Step 1 gives the identity on `H^0` under the kernel identification. I checked the identity and zero-sheaf cases and the trivial simplicial site: the differential alternates as expected and the collapse gives the ordinary derived direct image.

I searched the whole DAG and blueprint for the Stacks tags 0D79/0D7A and for augmentation spectral-sequence, total-site, and alternating-face statements. The helper differs from `lem-trf-simplicial-derived-image-spectral-sequence` because that node assumes scheme etale topoi and constant module coefficients; it differs from `lem-trf-total-site-derived-components` because that node compares component restrictions for a morphism of two total sites and has no augmentation E1 spectral sequence. No SGA source is cited. All proof steps are below 2000 characters and no compiler or build tool was run.

## Not duplicates

lem-trf-site-augmentation-spectral-sequence vs lem-trf-simplicial-derived-image-spectral-sequence: the existing node is restricted to simplicial scheme etale topoi and constant-module coefficients, whereas this helper applies to arbitrary small finite-limit sites and abelian sheaves and includes the canonical Cech comparison.

lem-trf-site-augmentation-spectral-sequence vs lem-trf-total-site-derived-components: the existing node states component restriction and unit comparisons for a morphism between two total sites; this helper states the augmentation spectral sequence for one total site and its base.

lem-trf-site-augmentation-spectral-sequence vs lem-trf-nearby-proper-hyperdescent: the existing node uses an augmentation spectral-sequence step inside a proper nearby-cycle argument but does not state the general spectral sequence or its hypotheses.

lem-trf-site-augmentation-spectral-sequence vs lem-trf-site-augmentation-acyclic-cech: the helper has no componentwise acyclicity hypothesis and only states the E1 spectral sequence and canonical comparison; the item adds the vanishing hypothesis, kernel identification, collapse, and derived isomorphism conclusion.
