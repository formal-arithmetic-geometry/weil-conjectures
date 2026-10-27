# Stage-1 report: lem-sfb-gm-fixed-square-zero-lifting

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-gm-fixed-square-zero-lifting.json: item, statement, split into five steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-gm-affine-action-grading.json: new statement-only input, unsplit; no Mathlib match. This gives the coordinate grading of an arbitrary affine multiplicative-group action, not fixed-point lifting.
- citations.json: verbatim statement extracts for every step citation.
- searches.jsonl: actual msearch.py queries and results. The node records preserve their query text and result records.

## Attachments

None. Searches by the item tag and by fixed-point lifting, multiplicative group, coaction, and grading in lean/WeilConjectures found no project declaration proving the whole item. Existing Mathlib formally smooth lifting declarations do not enforce fixedness. No Lean was written or compiled.

## WANTED

None. The relevant book PDF and the Stacks sources are present locally.

## Corrections and scope

The item statement is unchanged. The source correctly calls the arbitrary-base assertion agent-written: Milne's Theorem 13.1 and Lemma 13.6 concern varieties over a field and cannot themselves be cited as a theorem over an arbitrary ring. I read their actual printed pp.254--256. They motivate weight splitting, but the proof delivered here uses Stacks 0EKK and an explicit square-zero computation rather than claiming Milne supplies relative smoothness. The source-place phrase about a graded conormal argument has been replaced by weight-zero projection to describe the proof actually delivered.

The inherited blueprint ancestry has from.node = null and a long via chain; tools/blueprint_refs.py ancestor prints no blueprint ancestor. I retained that inherited route and named its precise supporting infinitesimal place, rather than inventing a blueprint ancestor. Searches of the whole DAG, blueprint_refs.py search (grading, graded, multiplicative, complete reducibility, square-zero, 0EKK), and latest blueprint found no node stating the new general affine grading assertion. The unit and chapter records were read; the item is not a unit key statement and changes neither record nor route. All source blueprint reading used literature/blueprint/latest/, including its current def-sbc-smooth-morphisms. That definition still supplies smooth-algebra lifting; the live DAG definition explicitly supplies the affine first-order lifting property used in step 3.

## Not duplicates

lem-sfb-gm-affine-action-grading vs lem-sfb-graded-stabilizer-strong-products: the existing statement starts with a grading and derives strong products from equality of two stabilizer ideals; the new statement constructs the grading of an arbitrary affine group action.

lem-sfb-gm-affine-action-grading vs lem-sfb-trivial-torus-coherent-weight-decomposition: the existing theorem assumes a Noetherian scheme over a field, trivial base action, and coherent linearized modules; the new statement concerns an arbitrary commutative-ring coordinate algebra with an arbitrary affine action, with no coherence or finiteness hypothesis.

lem-sfb-gm-affine-action-grading vs def-sfb-trivial-torus-coherent-data: the existing node defines linearizations and weight decompositions over a field, but asserts no decomposition-existence theorem for arbitrary affine coordinate algebras.

lem-sfb-gm-affine-action-grading vs lem-sfb-split-torus-torsor-section-extraction: the existing theorem extracts a twisted nonzero section from a torus torsor over a field; it does not state the grading theorem over arbitrary rings.

lem-sfb-gm-affine-action-grading vs lem-sfb-affine-free-split-torus-invariants: the latter concerns an affine fppf quotient for a free action over a Noetherian base; its grading is mentioned as notation, not asserted for arbitrary algebras and actions.

lem-sfb-gm-affine-action-grading vs lem-sfb-relative-torus-bundle-weights: the latter decomposes finite projective modules with a coaction. A smooth finite-type coordinate algebra need not be a finite projective module over its base (R[x] already is not finite), so that theorem cannot be applied here.

lem-sfb-gm-affine-action-grading vs lem-sfb-gm-representation-weight-basis: the latter assumes a field and a finite-dimensional representation; it does not cover an arbitrary coordinate algebra over an arbitrary base ring.

## Review by Q60

I read Stacks groupoids.tex, lemma-complete-reducibility-Gm (0EKK), its proof, and example-Gm-on-affine (0EKJ). The proof expands the coaction in the Laurent basis and compares the two-variable coefficients: each coefficient is homogeneous of its own weight, their finite sum is the original element, and the sum is direct. Multiplicativity makes products add weights. In the relative version the structural image of R has weight zero because the action is over Spec R. This verifies the source of the new node, including arbitrary base, absence of finiteness assumptions, R-submodule grading, unit, and homogeneous evaluation formula. The statement contains no proof sketch, only its hypotheses and conclusion, and introduces the Laurent ring and action explicitly.

Step 1 uses exactly that new grading statement and its homogeneous evaluation formula; the quoted conclusion in citations.json includes both. Step 2 uses the same formula, with B = B_0[z,z^{-1}] and its universal unit. Coefficient uniqueness, explicitly part of the new node's Laurent-ring convention, gives vanishing of each nonzero-weight image even over a finite field or ring with zero divisors. The converse is written out by finite additivity and holds after every algebra extension, not just at B_0-valued units.

For step 3 I opened and read the full statements of def-weil-closed-immersion, def-sbc-first-order-thickening, def-sbc-smooth-morphisms, and def-weil-affine-spectrum. The first explicitly identifies affine closed immersions with quotient spectra. The second says square-zero defining ideal is first order. The third explicitly promises a global lift against a first order thickening of affine schemes, and the fourth identifies affine morphisms with ring maps functorially. I also read more-morphisms.tex definition-formally-smooth (02H0). Thus both test schemes are affine, they carry the given R-structures, the immersion has ideal J and J^2 = 0, and the lift stays over Spec R. No local-to-global affine lifting theorem is smuggled into this step. The final f(C_n) containment follows from pf = g and step 2.

In step 4 I checked every homogeneous multiplication case. The only potentially problematic case is m+n=0 with m and n nonzero: here both f(a) and f(b) belong to J, so the degree-zero contribution is killed by J^2=0. The remaining cases use only the grading and f's algebra-map laws. Additivity and finite distributivity extend the homogeneous verification to all elements. This is a direct elementary calculation from previously established statements, not a separate hidden smooth-fixed-locus theorem. Step 5 uses the vanishing from step 2 to check ph = g, and its converse to verify universal fixedness. Every external node used by each step is named and has an exact statement quotation; proof_deps is their union.

I checked delivery-errors B--E: the sole new node is self-contained, statement-only and strictly below the item (no smoothness or lifting conclusion); it has the exact Stacks tags and labels, genuine logged Mathlib searches in two phrasings and grep, and blueprint from/same_as fields. The node is not the item under another name. No proof of another node is used as if it were its statement. All non-elementary input is the cited grading theorem, while smooth lifting is an explicit instance of the cited definition. All proof steps are shorter than 2000 characters. The inherited search results and metadata remain intact.

For small cases: with trivial action only C_0 survives, so h=f; with J=0 the construction returns g; the zero ring and empty affine scheme introduce no forced nonzero element or existence of an unavailable point; the universal-unit test works in every residue characteristic. Weights 1 and -1 on R[u,v] test the opposite-weight product: if the point has u=v=0 modulo J, f(u)f(v)=0, exactly as required. The projection C to C_0 is generally not multiplicative (uv illustrates this), but its composite with this particular lift f is multiplicative because J^2=0. This distinction is the key check of the proof, and is stated explicitly in step 4. No extra reductivity, connectedness, field or Noetherian hypothesis has been added. No statement dispute remains.

## Unfinished work

The new grading node is intentionally left unsplit for a later stage-1 item. Nothing in the assigned item's assembly proof remains unaccounted for.
