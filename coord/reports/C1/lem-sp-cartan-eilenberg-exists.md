# lem-sp-cartan-eilenberg-exists

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-exists.json`: split proof, no new nodes; Mathlib searches already recorded on the item found no Cartan--Eilenberg declaration.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I searched the project source for the item id, Cartan--Eilenberg terminology, and likely declaration names; no sorry-free project declaration states this existence result.

## WANTED

None. The Stacks source checkout is available at `/home/ubuntu/c1-stacks-review/derived.tex`, including Definition 015H and Lemma 015I.

## Corrections and limitations

The imported item had no proof. I followed the source construction: decompose the bounded-below complex into alternating short exact sequences of cycles, terms, boundaries, and cohomology; apply the existing horseshoe node inductively; define the horizontal differential through the quotient and cycle resolutions; and verify the Cartan--Eilenberg conditions. The assigned unit `sk-prop-av-pqf-finite` is unrelated to this spectral-sequence lemma, so I left the unit record unchanged. The existing horseshoe node is a tool use from another unit because it supplies the exact compatible-resolution construction required by the source route.

## Second reading by C1

- Item statement: checked Definition 015H and Lemma 015I in `derived.tex`, including bounded-below and nonnegative-index hypotheses; the resolution clauses agree.
- Step 1: checked against the alternating exact sequences in Lemma 015I and the abelian-category node; repaired the prose to use the supplied bound `n = 0` and state the kernel/image argument.
- Step 2: checked each horseshoe application against Lemma 013T and the injective-resolution definition; the induction uses the displayed short exact rows and negative-degree vanishing.
- Step 3: checked the quotient-to-subobject composite against the adjacent horseshoe rows and the double-complex definition; compatibility gives a chain map and exactness gives consecutive composite zero.
- Step 4: checked first-quadrant bounds and each cycle, boundary, and cohomology resolution against Definition 015H; repaired the prose to avoid an unjustified index shift and identify the adjacent rows used.
- New nodes: none; there were no new statements to audit for B1--B7 or duplicate/Mathlib status.

Changes made: clarified the lower-bound choice and exact-sequence justification in Step 1, and clarified the first-quadrant conclusion and adjacent-row identifications in Step 4.

## Review by C1

I read the item statement and its source at Definition 015H and Lemma 015I in `/home/ubuntu/c1-stacks-review/derived.tex:7105-7180`, and read the cited DAG statements in full. Step 1 uses only the abelian-category statement for kernels, images, quotients, and the alternating short exact sequences; the displayed definitions are the standard kernel/image decompositions of the differential. Step 2 uses the horseshoe node's exact assertion that three injective resolutions exist with compatible morphisms and degreewise short exact rows, together with the injective-resolution definition; its hypotheses are exactly an abelian category with enough injectives and a short exact sequence. Step 3 uses the same compatible rows to define the composite horizontal maps, and the double-complex node for the induced complex structure; the commutative horseshoe diagrams give compatibility with vertical differentials and the consecutive quotient-to-cycle composite is zero. Step 4 uses the horseshoe node for injectivity, exactness, and negative-degree vanishing, the injective-resolution node for the resolution conclusions, and the double-complex node for the first-quadrant condition.

I checked the small cases of a complex concentrated in one degree (the construction reduces to an ordinary injective resolution), the zero complex (the zero double complex), and the first nonzero degree n (the first two horseshoe rows give the required cycle and boundary resolutions). The existing horseshoe node was searched by its Stacks tag and keywords before citation; it differs from this item because it assumes one short exact sequence and constructs compatible resolutions, while this item iterates it to construct the full Cartan--Eilenberg double complex. No statement was weakened or duplicated.
