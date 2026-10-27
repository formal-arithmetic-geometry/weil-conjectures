# Stage-1 delivery: lem-sfb-compact-symbol-frequency-kernel

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-compact-symbol-frequency-kernel.json`: item split in six steps; statement unchanged, existing source, imported search records and ancestry retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-product-fubini-integral-swap.json`: statement, Mathlib leaf, `MeasureTheory.integrable_prod_iff` (Prod.lean:231–235) and `MeasureTheory.integral_integral_swap` (Prod.lean:482–484), one declaration for each clause.
- `dag/nodes/sec-six-functors-basics/lem-sfb-oscillatory-cutoff-convergence.json`: statement, Mathlib leaf, `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` (DominatedConvergence.lean:67–74).
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `searches.jsonl`: executed search log; the leaf search records are taken from actual results in this item's log.
- `report.md`: this report.

There are two new nodes and two Mathlib leaves. No new unsplit node, Lean file or unit/chapter record is delivered. The discarded, uncommitted integration-by-parts candidate is absorbed into the item's step 1 by the existing directional derivative identity; it is not part of this delivery.

## Attachments

None. The live `lean/WeilConjectures/` was searched for the item id, compact-symbol and frequency-kernel language, and pseudodifferential terminology. No declaration gives this item's conjunction. The upstream sorry-free attachment rule therefore does not close it. Existing Mathlib declarations supply ingredients, not the variable-symbol statement as a whole.

## Wanted literature

WANTED: Jean-Pierre Demailly, Hodge Theory, Part I §3.B, Theorem 3.6, printed p.13 (PDF p.25), for lem-sfb-compact-symbol-frequency-kernel. The seeded document `literature/demailly-hodge-ams.pdf` is absent locally; an attempt to read the author's `hodge-ams.pdf` URL timed out. I do not claim to have read this PDF. The proof is explicitly agent-written, using read Mathlib source statements as the analytic prerequisites.

## Faults found and corrections

The imported item had no proof, but its statement is true and is retained verbatim. The naive argument “the compact smooth Fourier transform decays” would fail to explain why the constant is uniform in the symbol parameter; step 1 instead computes the finite derivative bounds with their common factor `(1+|zeta|)^r`. The frequency-kernel exchange needs product integrability and Fubini, not only an integral norm bound; the first new leaf states both tools. The oscillatory limit needs a real parameter tending to infinity; the second leaf states dominated convergence along a countably based filter, rather than only along integer sequences. The dilation and the prefactor `(2 pi)^(-m)` are computed explicitly in step 5. There is no statement dispute or change of the target route.

The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor lem-sfb-compact-symbol-frequency-kernel` prints None. I retained that inherited value and complete via-chain, and extended it by the item id for the leaves. The latest blueprint's direct-images proof (3), at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, was read together with its current unit section. This item is the supporting Fourier estimate in the existing, already created Sobolev input chain, not a replacement of a unit step. The group does not edit ancestor nodes to fix their metadata.

## Unfinished work

No mathematical clause of the item remains unfinished. The two general tools are exact Mathlib leaves. The cited Demailly PDF remains wanted; its absence is disclosed in proof_origin and the source of every proof step.

## Not duplicates

Whole-DAG searches inspected statement text for Fubini, product measures, Bochner integrability, dominated convergence and the candidate declaration names. Whole-blueprint searches for Fourier, Bochner, product measure, Fubini, integration by parts, and dominated convergence found no blueprint statement of either new leaf; the Fourier hits concern finite-field Fourier–Deligne transforms. Existing uses of the word “Fubini” are category-theoretic iterated-limit/coend results, not measure theory. There is no Stacks tag on these analytic Mathlib leaves, hence no same-tag pair to distinguish.

lem-sfb-product-fubini-integral-swap vs lem-sfb-l1-bilinear-fourier-duality: the existing statement transposes scalar Fourier integrals with a fixed bilinear phase and two separate L1 inputs; it neither states the product-integrability criterion nor interchanges a general jointly dependent variable-symbol kernel.

lem-sfb-product-fubini-integral-swap vs lem-sfb-integrable-majorant-estimate: the existing statement concerns a single scalar integrand and a known integrable bound; it does not construct integrability on a product or exchange integration order.

lem-sfb-oscillatory-cutoff-convergence vs lem-sfb-dominated-integral-frechet-derivative: the existing statement differentiates a parameter integral with a dominated derivative; it does not assert convergence of arbitrary dominated measurable families along a filter.

## Review by Q120

I checked the split against delivery-errors B–E with the cited node statements open. For the item the named Demailly source was unavailable, so I checked the actual Fourier argument directly, rather than attributing an unread proof to the author. For the two new leaves I read the pinned local Mathlib sources at the exact lines recorded above. Prod.lean:231–235 has precisely the almost-everywhere section-integrability and integrability-of-the-integral-of-the-norm criterion. Prod.lean:482–484 requires product integrability and SFinite measures; Euclidean Lebesgue spaces are sigma-finite and satisfy this. DominatedConvergence.lean:67–74 has eventual strong measurability, an eventual almost-everywhere norm bound, an integrable real majorant and almost-everywhere convergence along a countably generated filter. Those are the written hypotheses of the new leaf, without strengthening the conclusion to pointwise convergence of the original oscillatory integral.

Step 1 uses exactly the compact-smooth-to-Schwartz clause of `lem-sfb-schwartz-test-inclusion-integrability`, the derivative identity of `lem-sfb-schwartz-fourier-l2-identities`, and the scalar norm-integral estimate of `lem-sfb-integrable-majorant-estimate`. I apply the derivative identity to scalar entries with Hilbert codomain C, so the matrix operator norm need not be a Hilbert norm. Its iteration has base order zero and step multiplication by `2 pi i theta_k`; the derivative support stays in the same closed K. The operator norm is bounded by the sum of the absolute values of entries, so the final constants remain uniform in zeta. No unattested decay theorem is cited. I checked theta=0, L=0, empty K, and p=0 or q=0.

Step 2 uses the actual S-to-S clause of `lem-sfb-schwartz-fourier-coordinate-rule`, and the integrability statement of `lem-sfb-euclidean-bracket-integrable` with s=M/2>m/2, followed by the scalar majorant leaf. The split into the unit ball and its complement derives the polynomial majorant from the seminorm definition. It proves absolute weighted integrability for every real exponent needed later, including negative symbol order. Finite-dimensional norms reduce this to scalar majorant applications; continuity supplies measurability.

Step 3 uses only the statement of `lem-sfb-dominated-integral-frechet-derivative` after step 2 has proved all its integrability bounds. The product rule includes derivatives of the exponential, giving the growth exponent r+|alpha|. Every derivative is dominated throughout a common neighbourhood (in fact globally in x), and the real Banach codomain is obtained by restricting scalars on a finite-dimensional complex vector space. The induction computes all derivatives; their continuity follows from existence of the next derivative. This does not silently infer smoothness from pointwise differentiability alone. Vanishing outside K is immediate from the original integral.

Step 4 uses the criterion and exchange clauses of the new product leaf and the existing scalar majorant estimate. Its product majorant is explicitly `1_K(x) w_r(xi)`; integrating the finite-volume factor verifies the criterion. The negative x-Fourier phase and positive quantization phase combine to eta-xi, and the b argument is still 2 pi xi. Moving a fixed vector through a finite matrix integral is finite linear algebra, written in the step. It proves the integral formula for every eta.

Step 5 uses the product/Fubini leaf and scalar majorant leaf for the finite-frequency regularization, then the precise `lem-sfb-euclidean-jacobian-integral` statement for the global diffeomorphism xi -> 2 pi xi. Its determinant is positive `(2 pi)^m`; this cancels exactly the original prefactor. It integrates f against the negative y phase at zeta/(2 pi), which is the definition of its transform, not an extra inversion theorem. The cutoff is retained throughout. The frequency factor is bounded on its compact support even when r<0. This step also applies when f has noncompact Schwartz support.

Step 6 uses the product/Fubini leaf, scalar majorant estimate and the general-filter dominated-convergence leaf. Its majorant includes the test and the bound B=sup|chi|, so it works for any fixed allowable cutoff, without positivity or a bound of one. The filter of positive real R tending to infinity has the countable cofinal base R>n. Applying dominated convergence on the product space proves convergence of every test pairing; summing scalar components gives the vector distributional equality. Every assertion taken from a node is in its statement; citations.json contains literal copies and no paraphrases.

For B1–B10, the two new statements introduce their own spaces, measures, codomains, filters and measurability assumptions; neither includes a proof sketch. Their status is mathlib, their proofs are empty, and every match records the declarations and source lines read. All recorded searches were actually run and returned hits; the incomplete Loogle experiment for the earlier discarded cutoff formulation is not treated as evidence of absence. No Stacks or forbidden SGA reference is used. For C1–C8, no step uses a node's internal proof, every analytical black box is a cited statement, proof_deps is exactly the union of uses, and all citations stay within this unit or its Mathlib tools. For D1–D5, the work is an argument for the item, while the new leaves are generic measure-theory tools, not relabelled clauses. For E1–E7, I checked the sign, Jacobian, support, matrix norms, parameter uniformity, smoothness induction and test-limit hypotheses just described. The statement is not weakened. Every step is below 2000 characters; no long-step exception is needed. No compiler, Lake or build tool was run and no agents were started.
