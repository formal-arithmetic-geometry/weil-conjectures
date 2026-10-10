# Delivery report: lem-weil-pbc-limit-fibre-products

## Files

- dag/nodes/sec-proper-base-change/lem-weil-pbc-limit-fibre-products.json
- dag/nodes/sec-proper-base-change/lem-weil-pbc-fibre-product-affine-transition.json

## Source review

The source is the general-case limit argument in the proof of Stacks Tag
0G7X, literature/stacks-project/perfect.tex, line 8166. The displayed
identity
X_s = X x_S s = lim X_i x_{S_i} s_i = lim X_{i,s_i}
is exactly the residue-field specialization in the third proof step. Its
categorical content is the existing imported node
lem-kun-fibre-product-limits, which records the universal-property proof
of the comparison isomorphism and the Categories Tag 002M citation.

The source leaves affineness of the induced transition maps implicit. I
made that reusable obligation explicit in
lem-weil-pbc-fibre-product-affine-transition: the map is factored using
the diagonal of the affine transition on the base, followed by base
changes and a composition of affine morphisms. This is the Stacks
Morphisms 01SD/01SC/01SG argument cited in the item and supplies the
affine-transition clause both for the full fibre-product system and for
the specialized scheme-theoretic fibres.

The residue-field limit is cited through
lem-weil-pbc-limit-residue-field; the scheme-theoretic fibre and fibre
product notions remain the existing statement dependencies. No existing
node with the new affine-transition statement was found.

## Review by G1

I checked the statement against the source: the hypotheses retain three
compatible inverse systems with affine transition maps, the conclusion
contains both the affine transition assertion and the limit
identification, and the final fibre clause uses the images s_i and the
residue-field limit without adding hypotheses. Step 1 invokes the
existing universal-property lemma for the canonical limit comparison.
Step 2 isolates the only omitted geometric detail in a public child node
and cites the exact Stacks permanence tags. Step 3 applies the same
comparison to Spec kappa(s_i) and uses the child for fibre transitions.
Every cited node exists and is unmerged; the only proof dependency
outside sk-thm-p1 is the imported generic categorical tool
lem-kun-fibre-product-limits, recorded in tool_uses.

## Validation

- python3 -m json.tool passed for both node files.
- python3 tools/review_split.py lem-weil-pbc-limit-fibre-products passed.
- python3 tools/check_dag.py --cycles reported 0 cycles and 0 self-loops
  (with pre-existing reachability notices).
- git diff --check passed.
