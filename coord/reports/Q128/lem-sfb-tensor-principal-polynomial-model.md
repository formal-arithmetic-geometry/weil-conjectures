# Q128: lem-sfb-tensor-principal-polynomial-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-tensor-principal-polynomial-model.json: statement, split; seven proof steps. Existing statement and statement dependencies retained verbatim. Existing search records retained; six actual Q128 searches appended.
- citations.json: nine step/node entries with verbatim statements.
- report.md: this report.

No new nodes; no new Mathlib leaves. All five distinct proof dependencies already exist and have status mathlib. The finite expansion, polynomial generator checks, and tensor map checks are steps, rather than new nodes.

## Attachments

None. Searched the entire project WeilConjectures source for the blueprint id and for tensor/principal/polynomial, polynomial pushout/specialization, and finite pure-tensor expansions. The hits concern other constructions, not a declaration giving all clauses of this item. No source declaration is treated as finished merely because its docstring describes the argument.

## WANTED

None. All sources used are present in literature/stacks-project/. No SGA source was used.

## What was wrong or missing

The assigned node had a statement and searches but no proof. Its statement is correct as written, including arbitrary commutative algebras, zero rings, and n=0. No statement correction or STATEMENT-DISPUTED claim is necessary.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints None. I retained that existing metadata, rather than inventing an ancestor or editing maintainer fields. The inherited from.place records an older alteration route. I read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its sk-thm-sf-ctf-stability-direct-images.proof.md; the current direct-images paragraph (3) proceeds through compactification and proper/open preservation. It does not state this finite polynomial auxiliary. The split_report.blueprint records that difference explicitly. This delivery changes neither a chapter/unit nor an ancestor's proof route; it completes the already assigned algebraic prerequisite of lem-sfb-polynomial-test-universally-open.

## Unfinished work

None in this stage-1 split. No Lean file was written, and no compiler, Lake, library build, or local preflight/check script was run.

## Searches and existing facts

Read Stacks more-morphisms.tex Tag 0F31 (lemma-test-universally-open), proof of (3) implies (1), affine paragraph at lines 21755–21784. Its A' is this item's B and its B is this item's C. This renaming is essential: variables specialize into B, while polynomial coefficients belong to C.

Read schemes.tex Tag 01I4 (lemma-fibre-product-affine-schemes), especially its universal-property proof, and Tag 01JQ (lemma-fibre-product-affines). Read morphisms.tex Tag 01S1 (lemma-base-change-surjective), whose proof states the image formula for arbitrary subsets, and Tag 0495 (lemma-when-point-maps-to-pair). Verified those labels against literature/stacks-project/tags/tags.

Read the statements of def-weil-pbc-module-tensor-product, def-weil-pbc-mv-polynomial-ring, def-weil-affine-spectrum, lem-weil-pbc-fibre-product-affine-spectra, and lem-weil-pbc-base-change-image in full. The image node genuinely includes arbitrary subsets, so no open-subset restriction or new image lemma is needed. The affine fibre-product node identifies the projection maps, so it supports the specified square, not just an abstract affine isomorphism.

Whole-DAG searches by titles, key concepts and Stacks tags found these existing nodes. Whole-blueprint searches with blueprint_refs.py for "tensor principal polynomial", "polynomial specialization", "finite tensor", and "base change image" found no equivalent imported item. The unrelated finite-tensor hit is cor-mg-det-weight-finite-tensor. Tag 0F31 also occurs in the already existing polynomial-test and principal-affine-test nodes and their universally-open parent; none supplies the present algebraic construction, and none is used to prove its own prerequisite.

All six Q128 Mathlib searches were made with msearch.py and their actual results are in searches.jsonl. Both semantic phrasings, both Loogle queries, LeanSearch, and grep were read. Read Mathlib/RingTheory/TensorProduct/MvPolynomial.lean:178: its IsPushout is the coefficient-extension square, not the evaluated-variable square. Read Mathlib/RingTheory/PolynomialLaw/Basic.lean:452: exists_lift produces an arbitrary polynomial-tensor lift, not the required linear h and specified spectrum identities. Read Mathlib/Algebra/Category/Ring/Constructions.lean:116 and the preceding colimit construction: they give the generic tensor pushout only. Thus none of those candidates states this entire item or gives it by one-line specialization. The inherited Q125 searches remain unchanged as history, not attributed to Q128.

## Not duplicates

No new nodes were created. Existing general statements are cited directly. In particular no new finite-expansion, tensor-ring-universal-property, cartesian-image, or polynomial-specialization node duplicates an existing node or restates an item clause.

## Review by Q128

I checked the statement against the affine paragraph of Stacks 0F31 with B and C renamed as above. The hypotheses there and in every cited node allow arbitrary commutative rings: no flatness, reducedness, finite generation or finite presentation enters. The construction needs only finitely many tensor summands for the one element g.

Step 1 uses exactly the tensor definition's assertion that pure tensors generate as a module. Absorbing each A-scalar into its first factor explains the finite pure-tensor sum; this is a short consequence, not a separate lemma.

Step 2 uses the tensor definition for balancing and the polynomial definition for existence and uniqueness of evaluation. I checked the two paths on A-coefficients and on every variable, and computed k(h) term by term. Thus agreement on generators and the displayed multiplication are sufficient; no polynomial/base-change theorem is assumed.

Step 3 uses the tensor universal property and polynomial universal property from those same statements. I checked that the target E need not initially be an A-algebra: the given compatibility supplies its common A-structure. That makes (b,c) ↦ v(b)u_0(c) A-bilinear. Unit preservation and the pure-tensor multiplication equality prove the linear lift is a ring map; expansion by finite sums extends multiplicativity to every pair of tensors. Compatibility on variables supplies wk=u, and the identity b tensor c=j(b)ell(c) supplies uniqueness. All these checks are written out; this is the argument for the item's pushout clause, not an appeal to an unrecorded ring-pushout lemma.

Step 4 uses the tensor definition to build F from S tensor_R B and uses step 3 to build its inverse G. I verified R-balancing using k phi_n=j e, the composite FG using the proved uniqueness, and GF on each pure tensor. The existing affine fibre-product theorem applies to the actual R-algebras S and B and identifies both projections. This avoids assuming that the underlying topological space is a set-theoretic pullback. The cited node states exactly the affine tensor model and its projections.

Step 5 is contraction of primes under the induced spectrum morphism: h is outside k^{-1}(p) precisely when k(h)=g is outside p. I use the spectrum definition for the induced morphism and spell out this definitional membership calculation. No assertion about inverse images of opens is left as an uncited non-elementary fact.

Step 6 uses only the existing base-change-image statement, with its arbitrary subset C specialized to D_S(h). I verified every corner and arrow, and substituted the step-5 inverse-image identity. The cited statement really does contain q(p^{-1}(C))=g^{-1}(f(C)) for every subset, not merely surjectivity of a base change. The letter C in that lemma denotes a subset, whereas C in this item denotes the coefficient algebra; the proof explicitly distinguishes them.

Step 7 checks the small cases. For g=0 choose n=0 and h=0; both principal opens are empty. Polynomial evaluation with no variables is the structure map, and the pushout is the ordinary tensor product. If either algebra or the tensor product is the zero ring, the same balanced pairings and uniqueness still apply, and empty spectra satisfy the image identities. No chosen prime, inverse or nonzero element is used.

For delivery-errors B, all cited notions have definitions or are explicitly given in the item; there are no unsplit new nodes, no proof sketches disguised as statements, and no new unsupported source tags. For C, I checked each cited statement, recorded every step/node pair verbatim in citations.json, and used existing Mathlib leaves for the two non-elementary geometric facts. For D, the proof actually constructs all maps and their inverses; it does not move an item clause into a new node. For E, I checked ring structures, scalar balancing, arrow directions, finite sums, zero rings and empty variables. Every step has a Boolean elementary judgement; no step exceeds 2000 characters or hides a comparison lemma. The statement, inherited searches, source fields and other maintainer-owned data were preserved.
