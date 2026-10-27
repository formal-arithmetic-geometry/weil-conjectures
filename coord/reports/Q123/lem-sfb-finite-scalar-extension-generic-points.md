# Stage-1 delivery: lem-sfb-finite-scalar-extension-generic-points

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-scalar-extension-generic-points.json — existing statement, now split into seven steps; no exact Mathlib match.
- citations.json — twenty entries, one for every step/node citation, quoting the cited statements verbatim.
- report.md — this report. searches.jsonl is the search command's own log.

No new nodes and no new Mathlib leaves. The proof reuses existing nodes rather than making duplicate leaves or elementary subclaims.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id and by scalar-extension/generic-point terminology, then inspected the generic/going-down candidates, including Curve/GenericModelAux.lean, Morphisms/FiniteNormalDenseEtaleGoingDown.lean and RingTheory/KrullDimension/GoingDown.lean. None states this whole item. The normal finite-map theorem assumes normal locally Noetherian schemes and proves going down on stalks; it cannot attach to the present arbitrary-scheme statement. The Mathlib results returned by the logged searches supply separate ingredients, not all clauses in a one-line specialization.

## WANTED

None. All sources used are available in literature/.

## Corrections and route

The mathematical statement is unchanged. Added the missing notion references for module tensor products, free modules and flat ring maps to statement and stmt_deps, since the imported statement already mentions all three. In particular its ring-flatness assertion should use the ring-map definition, not just the existing scheme-flatness definition. No target, chapter, unit, import flag or inherited search record was changed or removed.

The item had no proof. The new proof is explicitly agent-written: Stacks supplies general ingredients, while their application to this finite field scalar extension and the elementary coordinate computations are written here. ILO X 2.3 Step 2, printed page 150, diagram (2.b), is the upstream motivation, not a claim that ILO states the present more general lemma verbatim. Read that page via pdftotext (the extract begins with the printed page heading 150). It constructs scalar-extended induced schemes in the alteration argument. The existing parent uses this item in its step 5 (the ingredient was cut from its older step 10).

Read the chapter sec-six-functors-basics and the inherited unit sk-thm-sf-ctf-stability, including its constructibility/direct-image route. This lemma is a generic algebraic-geometric tool underneath that route, not a replacement for a unit-level step. tools/blueprint_refs.py ancestor returns a null blueprint ancestor for the inherited new-target chain; retained its from.node, exact ILO place and via list. Whole-blueprint searches for generic points, scalar extension, finite scalar and 00HS found no imported node stating this item. The DAG searches found the general going-down, affine fibre-product, spectrum-component and fibre-residue nodes used below.

## Not duplicates

No new nodes. Existing lem-sc-flat-going-down, lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-spec-irreducible-components-minimal-primes, lem-weil-pbc-finite-dimensional-domain-is-field, lem-weil-pbc-fibre-product-points and lem-weil-pbc-fibre-product-point-residue-field are reused. There are consequently no new/existing same-tag pairs requiring separation.

## Review by Q123

I read Stacks algebra.tex at lemma-flat-going-down (00HS), lemma-irreducible (00ES), and the local-ring paragraph identifying the residue field of a prime with the fraction field of its quotient (following 07BI). I read schemes.tex at lemma-fibre-product-affines (01JQ), lemma-open-fibre-product (01JR), and the full statement and beginning of the proof of lemma-points-fibre-product (01JT), including its residue-field sentence. The affine tensor-product theorem is 01I4, cited by 01JQ. I also read the tensor-product, free-module and flatness definition nodes against the coordinate computations. There are no new-node sources to review.

For step 1, I opened both lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra. The first explicitly identifies the open image with the intersection of the two inverse images; taking the second open and base open to be the entire field spectra gives exactly the desired inverse image. The second explicitly identifies both projection maps, not merely the object up to an unspecified isomorphism. All three rings are commutative algebras over F as required.

For step 2, def-pc-field-tower defines finite degree by vector-space dimension; def-weil-pbc-free-module gives the unique finite-coordinate expansion definition of a basis; def-weil-pbc-module-tensor-product gives the bilinear universal property. The proof gives both coordinate maps and checks their inverse identities. Selecting a basis in a finite-dimensional vector space is the usual elementary finite-span basis reduction. This is a computation, not a new lemma restating a clause. R need not itself be finite-dimensional over F.

For step 3, def-weil-pbc-flat-ring-map really defines flatness by preserving injective module maps after tensoring. The displayed mutually inverse maps identify the actual induced tensor map with the coordinatewise map. Thus no general preservation-of-exactness theorem, or free-implies-flat theorem, is silently cited from a definition. There is no need for finite presentation, reducedness or separability.

For step 4, I opened def-sc-generic-point, def-weil-irreducible-components and lem-weil-pbc-spec-irreducible-components-minimal-primes. The last states exactly the classification of spectrum components as V(q) for minimal primes; it does not state localization of generic points, so that passage is proved explicitly. For the reverse implication, every irreducible closed Z containing the closure of z meets O, and the nonempty relative open Z intersect O is dense; equality there implies equality after taking closures. For the forward implication, the closure in X of an irreducible enlargement in O contradicts maximality in X. The closure of a prime singleton is computed directly from the defining closed subsets V(I). No finite-component, sober-space or Noetherian theorem is hidden in this step, and no existence assertion about a generic point of an arbitrary irreducible closed subset is needed.

For step 5, I opened lem-sc-flat-going-down, which explicitly lifts any prime p_0 contained in the contraction of q to a prime q_0 contained in that particular q. Its sole ring-map hypothesis is flatness, supplied in step 3. Minimality of q forces equality, proving minimality of its contraction without an unsupported irreducibility inference. Step 4 then returns from the affine neighbourhood to V. This is the correct direction of going down; no going-up or dominance assumption is used.

For step 6, I opened lem-weil-pbc-fibre-product-points, def-weil-affine-spectrum, def-pc-scheme-fibre, def-pc-fibre-product, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-finite-dimensional-domain-is-field, and lem-weil-pbc-fibre-product-point-residue-field. The point lemma identifies the prime P in the tensor product of residue fields. Spectra of F and K have single points with exactly those residue fields, by the cited spectrum node. The fibre definition and fibre-product universal property identify W_x with Spec(kappa(x)) times over Spec(F) with Spec(K); the affine tensor theorem therefore gives Spec(D). The quotient D/P is spanned by the images of a finite basis of D and is a nonzero domain because P is prime. The domain-is-field node assumes only finite-dimensionality over a field, both now verified. Finally, the residue-field comparison node explicitly states the quotient-to-kappa(y) isomorphism when that quotient is a field, compatible with both scalar maps. This avoids the incorrect general assertion that a prime quotient always equals its residue field. This existing comparison is the one off-unit non-Mathlib tool and is declared in split_report.tool_uses, rather than writing a maintainer-owned top-level approval.

For step 7, def-weil-residue-field defines the maps through local-ring maps; the composite stalk map and induced maximal-ideal quotient maps give the claimed tower. The products of the two finite spanning families prove finiteness of the composite extension directly. The assumption on v applies to x by step 5; no assumption about images of all other points is substituted for it.

I tested the conclusion on the identity extension K=F, on the empty scheme and the zero affine ring, on a nonreduced scheme, and on a purely inseparable extension with kappa(x)=K (where the tensor product can be nonreduced). The basis and flatness calculations still apply. In the zero ring, 'free of rank n' is the exhibited finite free presentation R^n, not a claim of uniqueness of basis cardinality for the zero ring. For a split separable tensor product, different generic points may map to the same component generic point, which the statement allows. The proof never asserts injectivity on component sets or reducedness of D. All points with primes have nonzero quotient fields, and all empty cases are vacuous.

Against delivery-errors B–E: there are no new nodes requiring a standalone statement or new searches; all cited node statements were read, and every citation has a verbatim quote. Every non-elementary ingredient is a cited existing statement. The elementary steps give the coordinate or closure argument rather than referring to a tag as a proof. No clause is moved into a newly named node, no descendant is cited, and the residue-field assertion keeps the exact scalar maps. All seven steps are below 2000 characters. The retained Q28 search history is preserved, and five additional actual Q123 msearch calls (LeanFinder in two phrasings, Loogle, grep, LeanSearch) are appended from the command log; successful searches were not recorded as unavailable or vice versa.

## Repair of the landing refusal (2026-10-23)

The return concerns promotion of the side-project completion to the live queue, not a mathematical rejection. I compared the retained returned item with the current repository item: the current item is still unsplit, with empty proof and proof dependencies, while the sandbox holds the reviewed seven-step argument. The original statement, source, chapter, unit, creation record and blueprint ancestry agree, apart from the three explanatory notion references already documented above. The delivery tool rebuilds the commit against its freshly fetched current server DAG; the earlier delivery head is not reused.

I re-read every current proof dependency, including the complete fibre-product residue-field comparison rather than only its quoted final clause. All twenty retained quotes remain verbatim in their current statements, and every current statement still supplies the fact used in its step. No dependency needs replacement: the affine/open base-change lemmas retain compatibility with projections; going down still assumes only flatness; the minimal-prime lemma still covers arbitrary commutative rings; and the residue-field comparison still identifies the canonical map, not just an abstract field isomorphism. The definitions and the finite-dimensional-domain leaf retain the hypotheses checked in the original Review by Q123.

This repair also clarifies two arguments in the node. Step 3 now explicitly checks exactness coordinate by coordinate, matching the exact-sequence wording of Stacks 00HB as well as the cited node's injectivity definition. Step 6 now describes a map into the fibre as the pair of maps to the two field spectra, with its map to V forced by the first projection; this checks the fibre identification and its projection compatibility directly from the cited universal property. These are expansions of the existing computations, with no additional hypotheses, nodes or searches. Every step remains under 2000 characters. Identity, empty/zero-ring, nonreduced and purely inseparable cases still satisfy the formulas. The retained proof, citations, search results and earlier review are preserved.

## Unfinished work

None for the stage-1 split. No Lean was written and no compiler, Lake or build command was run. Independent review and later formalization remain the maintainer's workflow.
