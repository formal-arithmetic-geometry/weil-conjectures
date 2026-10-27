# Stage-1 report: lem-weil-pbc-finite-field-degree-isomorphism-transport

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-field-degree-isomorphism-transport.json: statement, split into five complete steps; not a Mathlib leaf as a whole.
- citations.json: eleven verbatim quotations for the eleven step/node pairs.
- searches.jsonl: four searches performed with the required launcher command in this session; read all outputs. Existing item search records were retained.

New nodes: 0. New Mathlib leaves: 0. No Lean files or repository files were written and no compiler was run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, finrank_eq_of_equiv_equiv and semilinear/basis/compatible-field-isomorphism concepts. There is no project declaration giving all the item's clauses. Mathlib's Algebra.finrank_eq_of_equiv_equiv states only algebraic finrank invariance; it does not supply the scheme-induced compatible isomorphism, arbitrary-basis assertion and finiteness equivalence together.

## WANTED

None.

## Findings and changes

The imported statement is correct and is unchanged. It was an unsplit auxiliary with no proof. The proof is now explicit about which algebra structures are used. No hidden scalar restriction is made: the inverse uses phi inverse, not phi. No finiteness assumption is used to prove the arbitrary-index basis equivalence. The source paragraph before Stacks 03J4 defines the degree; Stacks 03J5 motivates the auxiliary but does not itself print this full isomorphism-transport assertion. Accordingly proof_origin is agent, and the report does not attribute the expanded argument verbatim to that lemma.

Read SETUP's three-level rules, GOAL, the unit sk-thm-p1 and chapter sec-proper-base-change. Read the current main-20261015 ancestor at sk-lem-pbc-p1-injective-fibre/lemma-weil-pbc-h1-constructible-representation.md and its blueprint_update. This is a generic lower-level input below constructible generation and finite pushforward; no unit or chapter route was changed. Searched the whole DAG by title and statement for section-ring functoriality, basis/dimension isomorphisms and finite composition, and ran blueprint_refs searches for global sections, semilinear, finite morphisms and basis. Reused the existing exact Spec/global-section comparison and finite composition; no new node was warranted.

## Not duplicates

No new nodes, hence no new/existing node pairs. The item is more specific than the basic scheme-morphism definition, uses the existing Spec comparison and finite-composition nodes, and includes more clauses than the purely algebraic finrank theorem.

## Review by NP

I read Stacks schemes.tex at the ringed-space morphism discussion and Definitions 01HB/01IJ, Lemma 01HV (lemma-spec-sheaves), and Lemma 01I2 (lemma-category-affine-schemes). I read morphisms.tex at Definition 01WH (definition-integral), Lemma 01WK (lemma-composition-finite), and the paragraph before Definition 03J4 together with Lemma 03J5. Checked their labels against tags/tags. There are no new nodes requiring another source review. The linear calculations are supplied by me rather than attributed to an unprinted source proof.

For step 1, I opened def-weil-locally-ringed-space-morphism. Its statement specifies both the ring maps on opens and their composition. Evaluating on the full open gives the contravariant composition formula, and applying it to the actual inverse of u gives both inverse identities. This uses the definition, not a theorem missing from the citation.

For step 2, I opened lem-weil-pbc-spec-map-global-sections. Its equation is exactly the equation identifying j sharp with phi under the canonical section-ring identifications. The commuting square then gives e alpha = beta phi. Multiplication gives semilinearity, and substituting a = phi inverse(b), v = e inverse(w) proves the stated inverse formula. I also read Mathlib Scheme.ΓSpecIso_naturality and ΓSpecIso_inv_naturality at Scheme.lean lines 609 and 615 to check the direction of the canonical identifications.

Step 3 cites no external fact: the proof writes both spanning and independence arguments as finite sums, in both directions. Bijectivity of phi and e was already proved. The coefficients are transformed by phi in the forward direction and phi inverse in the reverse direction. Thus it does not mistake a semilinear map for a linear map over the same field.

For step 4, I opened def-weil-finite-integral-morphism, def-pc-scheme, def-weil-locally-ringed-space-morphism, def-weil-affine-spectrum and lem-weil-pbc-finite-composition. The finite definition requires affine inverse images and finite section-ring maps on every affine open. Restricting an isomorphism and its inverse to such an open proves both requirements directly; the ring target has generator 1. Spec's functoriality gives j inverse = Spec(phi inverse). The finite-composition node actually states composition of finite scheme morphisms, with no extra base hypothesis. The displayed factorizations use the original square, and two compositions in each direction give the finiteness equivalence. No unsupported finiteness-invariance lemma is silently invoked.

For step 5, I opened lem-weil-pbc-finite-over-field-affine-finite-dim, def-weil-vector-space-dimension and def-weil-pbc-fibre-degree-bound. The first explicitly uses the structure-map algebra and gives finite-dimensionality for any field and finite scheme. Both h and q meet its hypotheses by step 4. The dimension definition explicitly counts a basis, and the degree definition explicitly uses global sections with the given structural algebra. A finite spanning-list reduction constructs a finite basis; step 3 carries precisely that basis to the other space. This proves dimension equality without adding nonemptiness or reducedness hypotheses.

I checked the B--E return cases against the written split: objects and hypotheses remain self-contained; all substantive imported inputs are existing nodes whose statements were read; citations.json contains verbatim substrings; no dependency is used for a claim stated only in its proof; no new node restates a clause; no cycle or new node is introduced. All steps are below 2000 characters. Tested the empty scheme/zero algebra (empty basis, degree zero), the identity square, nontrivial field automorphisms, arbitrary infinite basis index sets, and finite nonreduced algebras such as K[epsilon]/(epsilon^2). The finite basis calculation retains nilpotents and hence degree, rather than merely counting points. No statement dispute was found.

## Unfinished

No mathematical part remains. Server validation and direct delivery are performed after this report is written.

## Validation repairs

The first dry run rejected the finite-composition quotation because the extracted conclusion was shorter than 40 characters. Replaced it with the entire cited statement, including its two finite-morphism hypotheses; no mathematical change.
