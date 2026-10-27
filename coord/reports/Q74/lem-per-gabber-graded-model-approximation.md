# Q74: lem-per-gabber-graded-model-approximation

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-graded-model-approximation.json: item, split into nine steps; statement and original searches retained, fresh searches appended.
- dag/nodes/sec-deligne-laumon-a1/lem-per-higher-graded-cokernel-perturbation.json: statement-only algebra lemma, unsplit; no Mathlib match after LeanFinder, Loogle, LeanSearch and source grep, with a second semantic phrasing. This is one new node and zero Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the twelve node uses in the item's steps.

The helper write_split.py and searches.jsonl are sandbox working records. No Lean was written, compiled or built. No repository or launcher file was changed and no git command was run by the worker.

## Attachments

None. I searched lean/WeilConjectures for the item's exact blueprint id, Gabber, thickened graded algebras, graded model approximation and perturbation of cokernels. The hits concern affine etale comparison, ordinary associated-graded ideal approximation, and finite-projective graded colimit descent. They do not state this item. I also searched for the new algebra statement before creating it.

## WANTED

None. The cited ILO PDF and Stacks source are present.

## Corrections and limitations

The item is faithful to ILO III Definition 4.2 and Theorem 5.1, including the fixed model, all later indices, uniform constants, N=n+1, a=N-c, and uniqueness over the specified thickening map. Its statement was kept. No repair note was present and no earlier sandbox split or report existed.

The source's affine reduction is made explicit without replacing the fixed model: choose finite affine charts on that model, present their coordinate rings, and descend only the finitely many coefficients of their syzygy matrices. Thus no unjustified assertion that a newly constructed model agrees eventually with the supplied model is needed. In particular no exactness over an intermediate A_alpha is assumed, in accordance with ILO Remark 5.3. No intersection of two affine charts is assumed affine.

## Source error

STATEMENT-DISPUTED (auxiliary source assertion only): ILO III Proposition 4.5(ii), as printed for an arbitrary ideal of a Noetherian ring, asserts exactness of the perturbed complex. This can fail away from V(I). Let B=k x k, I=k x 0, L=0, M=F=B, r=0, p=id_B, r'=0 and p' multiplication by (0,1). Take c=n=0. The original complex is exact at M, both original maps have Artin-Rees constant zero, and p-p' has image I. But ker(p')=I is nonzero whereas im(r')=0. Hence the perturbed complex is not exact. Stacks 07VE explicitly assumes I is contained in the Jacobson radical for its exactness conclusion.

The item does not assert perturbed exactness, and the new node explicitly excludes that conclusion. The higher graded comparison in ILO 4.5(iii)-(iv) remains valid with an arbitrary ideal: the transferred image bound uses a finite correction, and the quotient equality uses that bound. Neither part needs the infinite intersection argument. Adding the Jacobson hypothesis to the new node would prevent its application to B=completed A[t], so I have not silently used the more restrictive existing 07VE node. The item itself needs no statement correction and its geometric route is unchanged.

## Not duplicates

lem-per-higher-graded-cokernel-perturbation vs lem-sfb-perturbed-image-artin-rees-bound: the existing node assumes I is contained in every maximal ideal and concludes a transferred image bound only. The new node compares every width-a graded cokernel subquotient for congruence modulo I^(n+1), imposes no Jacobson hypothesis, and includes the quotient-algebra comparison when F=B; the polynomial-ring application is not covered by the existing statement.

lem-per-higher-graded-cokernel-perturbation vs lem-sfb-adic-relation-matrix-initial-ideals: the existing node assumes a local ring and its maximal ideal, F=P, and concludes equality only modulo the next power (width one), for some unspecified closeness exponent. The new node uses an arbitrary ideal in an arbitrary Noetherian ring, finite free F, a prescribed Artin-Rees loss c, and every width n+1-c. Neither a polynomial ring over a local ring nor its ideal mB meets the local/maximal hypotheses in general.

lem-per-higher-graded-cokernel-perturbation vs lem-sfb-artin-object-graded-approximation: the existing node constructs algebraic approximations of an object of a limit-preserving fibred category over a complete local ring. It does not state perturbation of two supplied matrix complexes or higher-width identity-induced graded quotients.

lem-per-higher-graded-cokernel-perturbation vs lem-per-rig-smooth-presentation-perturbation: that statement needs completed polynomial rings and a conormal power-splitting condition, and concludes an isomorphism of the whole quotient algebras. No rig-smooth or conormal condition is available here, and the new node only compares graded quotients for arbitrary finite free complexes.

lem-per-higher-graded-cokernel-perturbation vs lem-per-gabber-graded-model-approximation: the item is a uniform approximation theorem for a supplied geometric model, including all indices, canonical thickenings, comparison of A and its completion, and unique gluing. The new node has no local base ring, completion, coefficient stages, models, approximation maps or sheaves: it is the algebraic perturbation input of ILO 4.5. The item's steps construct the presentations, syzygies, common bounds, specialization and sheaf gluing rather than relabeling its conclusion.

The whole-DAG searches included Artin-Rees, 07VE/07VF, higher graded cokernels, perturbations and associated-graded approximations. Whole-blueprint searches with tools/blueprint_refs.py used graded, Artin, higher graded, higher associated, thickened normal, higher graded cokernel, approximate complex, perturb and perturbation. No imported blueprint node states the new algebraic fact. The nearest ancestor and its via chain were read and retained; the current latest ancestor proof was read. These are generic algebraic tools on the existing uniformization/approximation branch, not a change of the perverse-unit route.

## Review by Q74

I read ILO Expose III sections 2 and 4 (including Definition 4.2 and Proposition 4.5) and Theorem 5.1 with its proof and Remark 5.3, printed pp.35--42. For the new node I checked the displayed common-subquotient formula in 4.5(iii) and its two cases q<=c and q>c, the algebra clause (iv), and Stacks more-algebra.tex 07VE (lemma-approximate-complex) and 07VF (lemma-approximate-complex-graded). I also read Stacks algebra.tex 00FN (lemma-Noetherian-permanence), 00FP (lemma-Noetherian-finite-type-is-finite-presentation), 00IN (lemma-Artin-Rees), 00MA (lemma-completion-tensor), 0316 (lemma-completion-Noetherian-Noetherian), and 05GG (lemma-hathat-finitely-generated). The last is corroboration only; the proof uses the existing local-completion-quotient node, whose complete statement I opened, to get every finite quotient by applying it to A/m^k.

For step 1 the completion-quotient node really gives the kernel J times completed A for every surjection out of the Noetherian local A, so applying it with J=m^k is legitimate. The target quotient has nilpotent maximal ideal and its completion is itself directly from the compatible-sequence definition. The fibre-product node gives the universal property used to identify the thickenings. This step proves all-power compatibility; it does not misread the weaker adic-completion-mod-ideal node as an all-power assertion.

For step 2 I opened the finite-type-morphism definition, whose affine-cover clause supplies a finite cover with finite-type coordinate rings. The finite-type-algebra-noetherian node applies first to the finite-type A-subalgebra A_alpha0, and the finite-type-noetherian-finite-presentation node then gives finite polynomial relations on each chart. The base-change presentation follows by its explicit generator-and-relation universal property, written in this step. No faithful flatness of a stage inclusion is used.

For step 3 I opened the completion-noetherian, finite-type-algebra-noetherian and noetherian-submodule-finitely-presented statements. They respectively make completed A Noetherian, its polynomial ring Noetherian, and the kernel of a finite row matrix finitely generated. The kernel generators yield the required finite R matrix. All these facts hold with zero ranks and the zero quotient algebra. The Noetherian-submodule node is about arbitrary submodules of finite modules, not just ideals, so it supplies exactly this kernel claim.

Step 4 is coefficient bookkeeping in a directed union of inclusions. Finitely many polynomial coefficients occur. The product equations remain true in the chosen subalgebra by injectivity, and applying u preserves them. This does not claim that its syzygies remain generating over A_alpha or after u.

For step 5 I opened the Artin-Rees node: it supplies an inclusion in I^(j-c) times the image and permits enlarging the constant. Writing such an image element as a finite sum and lifting each image term proves the needed bound with a preimage in I^(j-c) times the domain. Taking a maximum works for both matrices on the finite chart cover and is independent of every later stage and every u. This is precisely why the threshold is uniform.

For step 6 I reread the entire new node's statement. Its im(r)=ker(p), p'r'=0, two image bounds and both map-difference bounds are all supplied before invoking it. N>=c+1 gives n=N-1>=c and a=N-c>=1. Its F=B algebra clause supplies multiplicativity, not just a module isomorphism. Its identity-induced degree-zero map is the canonical reduction map. The base graded map is the one identified in step 1.

For step 7 I opened both localization statements. Localization-quotient-commute identifies the displayed quotients on basic opens, and localization-module-exact preserves their kernel subquotients. Thus the polynomial quotient comparison with the completed chart gives sheaf isomorphisms. This step writes the actual quotients modulo every m^k; it does not assume that arbitrary nonflat base change commutes with all associated graded pieces.

Steps 8 and 9 use the definitions and the sheaf axiom. I checked generation also in negative degrees: for -a<q<=0 the degree-q base class of 1 times degree-zero v represents v modulo I^(q+a); for q<=-a the module is zero. For q>0, the ideal m^q O is generated locally by images of m^q with degree-zero coefficients. Therefore all graded maps with the fixed structural and degree-zero maps agree, on arbitrary restrictions. The local isomorphisms agree on overlaps without assuming those overlaps affine. For gluing, glue their values on each local section by the sheaf axiom; uniqueness makes the resulting functions additive, multiplicative, base-linear and restriction-compatible, and the same construction glues the inverses. The two composites are identities because they are so on every chart.

I tested the item with m=0, X empty (including an empty fixed model), X affine space, zero relations, unit ideal relations, nonflat quotients such as A/(t^d), and N=c+1. For m=0 all positive ideal powers vanish and the assertion reduces to the identical model; negative graded pieces have the prescribed zero/nonzero range. Empty chart covers allow c=n0=1. Nonflatness requires no extra hypothesis because we compare presentations and all quotient kernels, not tensors of filtered pieces.

For the new node I tested I=0 and I=B, q<=-a, -a<q<=0, q=0, and zero-rank modules. If I=B every graded piece is zero; if I=0 the differences are zero and the two subquotients agree. For q<=-a the common denominator is all F. No claim about perturbed exactness is made. The B=k x k example above confirms why that extra conclusion would be wrong.

The argument left for the new node is the genuine matrix perturbation lemma of ILO 4.5, not a clause of the geometric item. For clarity I verified its Jacobson-free bound directly: for y=p'(x) in I^j F, repeatedly improve a preimage x_s in I^s M while s<j-c. Since p(x_s) lies in I^(s+c+1)F, the original p-bound gives e in I^(s+1)M with p(e)=p(x_s). Write x_s-e=r(b), choosing b in I^(s-c)L when s>=c using the r-bound. Replace x_s by x_s-r'(b)=e+(r-r')(b), which lies in I^(s+1)M and has the same p'-image. This is a finite induction. It transfers the image bound without any separation hypothesis. For q<=c, p-p' lies in I^(n+1)F contained in I^(q+a)F, so replacing p(x) by p'(x) proves the required inclusion. For q>c choose a preimage in I^(q-c)M; its error lies in I^(n+1+q-c)F=I^(q+a)F. Reverse the roles using the transferred bound. When q+a<=0 the equality is tautological. The resulting identities are identities of subquotients of F, so are compatible with the base grading and multiplication for F=B. The node's proof remains empty as required for a new unsplit node; this explanatory verification is only in the report.

Every non-elementary step cites the statements it uses, with twelve verbatim quotations in citations.json; definitions and elementary ideal/quotient computations are written out. All nine steps are shorter than 2000 characters (largest 1033), so no long-step lemma is hidden. I checked delivery-errors B1--B10, C1--C8, D1--D5 and E1--E7 against these files and sources, including the non-Jacobson issue, the fixed-model issue and overlap affineness. Generic off-unit completion tools are explicitly declared in split_report.tool_uses; the other reused algebra and localization nodes are Mathlib leaves. No SGA source is used.

## Unfinished work

Only the new statement-only perturbation node remains for a later stage-1 worker, as required by a one-level split. No required part of this item's proof remains unwritten. The delivery is subject to the required server dry run and push.
