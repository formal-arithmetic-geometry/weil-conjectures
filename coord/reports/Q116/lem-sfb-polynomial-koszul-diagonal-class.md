## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-koszul-diagonal-class.json`: item, split into eight steps; retained its statement and earlier search evidence.
- `dag/nodes/sec-six-functors-basics/lem-sfb-koszul-evaluation-pasting.json`: statement-only algebraic lemma; no Mathlib match. It concerns arbitrary successive Koszul-resolved quotients, not relative dualizing complexes or a diagonal class.
- `citations.json`: one verbatim statement quotation for every citation in every item step.
- `searches.jsonl`: real msearch command log; queries and actual returned names recorded in the new node.

## Attachments

None. Searched the live read-only `lean/WeilConjectures/` for the item tag, graph/Koszul diagonal terminology, and nearby dualizing declarations. The smooth-diagonal and Koszul regular-immersion files do not state the flat, possibly singular polynomial-presentation construction with its scalar and refinement clauses.

## WANTED

None. The Stacks sources used here are present locally. The additional canonical-map compatibilities are explicitly agent-formulated, rather than attributed verbatim to the sources.

## What was wrong or incomplete

The supplied item was statement-only and its source explicitly marked the compatibility assertions as additional to the cited tags. Tag 0E2E supplies the polynomial/diagonal existence argument, but does not fix the graph generator. Tag 0BZJ proves only an isomorphism after polynomial refinement, and the footnote in Tag 0BZI explains why top differentials are needed to make it canonical. Merely citing those assertions would leave the specified-map clauses unproved. I kept the statement and wrote the graph/evaluation construction, including the quotient factor and the coefficient factor separately.

No statement dispute or change of route is needed. The newest blueprint is the `latest` symlink (COMMITS.txt records main-20261023-1620, 7284bb09). I read `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` there. The latest direct-image proof (3) uses the coefficient direct-image package; this item's existing algebraic-duality prerequisite chain is more detailed than that blueprint text. I preserved its chapter/unit and blueprint ancestor/via fields, whose nearest imported ancestor is null as reported by `blueprint_refs.py ancestor`. Searches of the whole imported blueprint for Koszul, graph, coinduction, Koszul evaluation and Koszul trace found no node stating the new pasting lemma.

## What remains

The one new lemma is deliberately unsplit. Its future worker must prove the algebraic signed trace-pasting assertion; it is not presented as a finished Lean proof. No Lean was written and no compiler, Lake or build tool was run. The repository and launcher were read only; all authored files are in the assigned sandbox.

## Review by Q116

I read Stacks `dualizing.tex`, the construction preceding Tags 0A70/0A71 and the two lemmas themselves, the coinduction-composition lemma between them, Tag 0BZI including its canonical-top-differential footnote, the proof of Tag 0BZJ, and the proof of Tag 0E2E. I also read `more-algebra.tex` Tag 068X and Tag 0A6A: perfectness of the source of derived Hom, rather than flatness of the scalar map, is what makes the relevant exchange invertible. For the new lemma I read `more-algebra.tex` Tags 0624, 0625 and 0628 and `duality.tex` Tag 0BQZ, including its signed dual calculation. Those are inputs to its eventual proof, not claims that its full naturality/pasting assertion occurs there.

Step 1 uses the finite-type Noetherian lemma to justify Noetherianity of B before the flat-polynomial-quotient perfectness lemma. That lemma gives the bounded finite-projective resolution it needs. The polynomial differential basis lemma gives the actual ordered volume, not just a rank-one line. The perfect coinduction exchange statement gives both invertibility and its counit characterization. Flat-tensor exactness justifies the Tor-independent tensor identity; the base-change factor is B_2 and the coinduced quotient is B_1. I corrected the draft to include the Noetherian-algebra citation explicitly rather than tacitly assuming its conclusion.

Step 2 uses the coinduction adjunction and right-adjoint composition for the pasted evaluation counit; their statements explicitly give that characterization. The graph-coinduction lemma supplies the augmented bounded finite-free graph resolution, including n=0. The new lemma supplies the specified top evaluation as a D(B) isomorphism and its action. Step 3 uses the actual formulas in the total-Hom coinduction statement to identify multiplication by the adjunct with kappa inverse. It is marked elementary because the calculation is b times the image of 1, written out; no uniqueness theorem for dualizing objects is substituted for this calculation.

Steps 4 and 5 use perfect exchange for P->B and for the graph/base-change rings, and use its explicit successive-base-change and counit clauses. I checked that the diagonal itself is never assumed perfect over A: the perfect resolutions are over P and T. R-flatness of B implies B tensor_R^L R'=B', even for a nonflat R'. A is B_2-flat and B is the coefficient B_2-module, which verifies the T-square Tor hypotheses. Differential base change gives the specified volume line. The adjunction/transitivity statements and the total-Hom formula identify the pasted mates by evaluating at 1 twice; the new lemma gives the trace square. Taking adjuncts then proves equality of the classes, rather than merely that the pulled-back class is a generator.

Step 6 cites localization flatness and exactness to keep both the quotient resolution and the graph resolution exact. It cites perfect exchange and the new trace statement for the specified comparison, and differential localization for the coefficient line. I checked that simultaneous B-localization changes both diagonal factors: A_(h_1 h_2), not just one of them. Inverting h in P while its B-image is a unit leaves the quotient B unchanged. A finite list is handled by composition; localization at zero is allowed and gives the zero-ring case.

Step 7 uses the existing polynomial-refinement lemma only for the isomorphism through the evaluation quotient. Its statement expressly does not give lift independence, so I do not take that from it. The new lemma fixes the normalization and pasting. The displayed identity a(x)-a(bar x)=sum b_i(x)(x_i-bar x_i) is ordinary repeated polynomial subtraction, including constants and arbitrary zero divisors. It exhibits the triangular matrix of determinant 1, and the differential basis formula gives the top-wedge identity. These verify the hypotheses of the new lemma without assuming B is an lci quotient of P. Adjunction then gives the class equality.

Step 8 takes the scalar endomorphism isomorphism, pseudo-coherence and finite R-Tor amplitude from the exact statement of polynomial relative perfectness, after trivializing the volume. It does not take canonical refinement independence from an abstract existence theorem. The ratio of the two class-preserving comparisons is a scalar b; the constructed normalized diagonal class forces b=1. This proves equality in D(B), not just after forgetting its B-action. The same uniqueness proves ordered composition coherence. The source theorem is used as a generic algebraic tool; all off-unit statement tools are listed in split_report.tool_uses.

I tested the new statement with r=0, s=0, S=0, a tuple containing a unit, one non-zero-divisor, and two ordered non-zero-divisors. A tuple of zeros is excluded unless its Koszul augmentation really is a quasi-isomorphism. I made the tensor-shift sign explicit: the coefficient comparison on the two shifted top generators includes (-1)^(rs), compensating their interchange in Hom currying. In particular r=s=1 has the minus sign, while an empty block has sign +1. The statement includes no flatness hypothesis on S->S'; it instead requires the exact Tor-independence needed for the base-changed augmented Koszul complex. It includes no unsupported assertion for a base change that destroys the resolution. For the item, n=0, B=0, R'=R/I and h with unit image all have the indicated constructions. The proof has no step longer than 2000 characters; the nontrivial general pasting fact is a separate statement-only node, not hidden inside the refinement step.

For delivery-errors B--E: the new node introduces every ring, tuple, line, quotient, comparison and hypothesis, uses TeX, and contains no proof steps or proof sketch. Every non-elementary item input is a cited statement; citations.json quotes those statements verbatim. I checked cycles through the principal existing duality tools and found no path back to this item. The new node gives a general regular-quotient trace law and is not any clause of the item: the item's proof still constructs beta, kappa and xi, verifies its Tor squares, derives class compatibility, writes the polynomial triangular calculation, and proves lift independence. Searches found only ordinary exterior pairing, determinant, cotangent and finite-algebra trace results in Mathlib. I read the exterior pairing formulas, the ordinary dual-base-change equivalence, and the regular-sequence file whose TODO lists Koszul regular sequences; none is a derived trace-pasting theorem. No search was invented or recorded as successful while unavailable.

## Not duplicates

lem-sfb-koszul-evaluation-pasting vs def-sc-koszul-conormal-comparison: the existing statement concerns Determinant-normalized Koszul conormal comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs def-sc-koszul-dual-complex: the existing statement concerns Total dual Koszul complex; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs def-sc-signed-module-dual-complex: the existing statement concerns Signed module dual of a chain complex; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-pc-chain-cone-coordinates-iso: the existing statement concerns Assemble scalar cone coordinates after extension by zero; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-pc-koszul-coordinate-cone-iso: the existing statement concerns A sheafified Koszul coordinate is a scalar mapping cone; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-basis-dual-matrix: the existing statement concerns Affine sheafification preserves transposed dual-basis components; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-closed-immersion-coefficient-square: the existing statement concerns Affine closed immersion coefficient square; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-finite-free-coefficient-comparisons: the existing statement concerns Degreewise finite-free affine Hom comparisons with arbitrary coefficients; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-finite-free-dual-complex-comparison: the existing statement concerns Affine sheafification commutes with degreewise finite free signed duals; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-finite-free-dual-naturality: the existing statement concerns Explicit finite basis affine dual comparisons commute with precomposition; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-coefficient-hom-coordinates: the existing statement concerns Underived affine Koszul Hom coefficient square; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-finite-free-resolution: the existing statement concerns Sheafification of an augmented affine Koszul complex; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-hom-coefficient-complex-square: the existing statement concerns Affine Koszul Hom coefficient complex square; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-hom-coefficient-homology-square: the existing statement concerns Homology transport of the affine Koszul coefficient square; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-hom-complex-iso: the existing statement concerns Affine finite free Koszul Hom complex coordinates; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-hom-coordinates: the existing statement concerns Homology of the affine Koszul Hom model; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-affine-koszul-scalar-ext-comparison: the existing statement concerns Affine scalar Ext as associated dual Koszul homology; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-clopen-rank-strata-formality: the existing statement concerns Formality of arbitrary module families on finite clopen rank strata; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-clopen-rank-strata-homology-lift: the existing statement concerns Lifting a single-degree map on one clopen rank stratum; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-closed-immersion-ext-ideal-action: the existing statement concerns Closed-immersion ideal annihilates scalar Ext; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-closed-immersion-rank-strata-scalar-formality: the existing statement concerns Scalar derived reconstruction on disjoint closed rank supports; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-closed-immersion-rank-strata-scalar-homology-lift: the existing statement concerns Lift a scalar homology map from one closed rank support; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-closed-immersion-ranked-cohomology-reconstruction: the existing statement concerns Finite rank-stratum reconstruction over a closed-immersion algebra; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-free-sheaf-dual-transpose: the existing statement concerns Canonical finite free sheaf duality transposes matrix components; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-k3-affine-hom-comparison-finite-free: the existing statement concerns Finite-basis inverse for a natural Hom comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-k3-affine-hom-comparison-maps: the existing statement concerns Natural forward affine Hom comparison, invertible in rank one; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-coefficient-extension: the existing statement constructs localization coefficient maps and explicitly does not compare normalized evaluations; the new statement compares evaluations and pastes two quotient adjunctions, for Tor-independent scalar maps too.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-complementary-equivalences: the existing statement concerns Signed complementary Koszul equivalences; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-conormal-comparison-existence: the existing statement concerns Existence of the determinant-normalized dual Koszul comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-conormal-top-homology-pos: the existing statement concerns Positive-rank top cohomology of a normalized conormal comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-conormal-top-homology-zero: the existing statement concerns Rank-zero top cohomology of a normalized conormal comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-conormal-top-homology: the existing statement concerns Top cohomology of a normalized conormal comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-derived-dual-evaluation: the existing statement concerns Signed Koszul dual homology and evaluated derived morphisms; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-dual-below-top-homology: the existing statement concerns Dual Koszul cohomology below the top degree; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-dual-conormal-rank-stratum: the existing statement concerns Finite locally free dual conormal on its rank stratum; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-coefficient-stalk-iso: the existing statement concerns Local top-degree Koszul coefficient map is bijective on stalks; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-constant-rank-top: the existing statement concerns Top Koszul Ext on a constant-rank open; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-determinant-multiplication: the existing statement concerns Intrinsic Ext determinant is quotient-linear; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-determinant-roof: the existing statement concerns Intrinsic Ext determinant satisfies the normalized roof formula; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-dual-homology: the existing statement concerns Ext is computed by the signed dual Koszul cohomology; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-off-rank-stalk: the existing statement concerns Off-rank stalk vanishing of pulled-back Koszul Ext; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-rank-support: the existing statement concerns Reconstruction of pulled-back Koszul Ext from its rank stratum; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-ext-roof-representatives: the existing statement concerns Roof-normalized Ext comparison with signed Koszul dual homology; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-normal-determinant-qcoherent: the existing statement concerns Quasi-coherence of the Koszul normal determinant; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-normal-determinant-term-qcoherent: the existing statement concerns Quasi-coherence of each Koszul normal determinant term; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-algebra-dual-homology: the existing statement concerns Algebra-valued Koszul cohomology sheaf comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-algebra-dual: the existing statement concerns Algebra-linear Koszul comparison for a regular immersion; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-derived-hom: the existing statement concerns Derived Hom for a Koszul-regular closed immersion; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-ext-pullback: the existing statement concerns Pullback of scalar Ext for a Koszul-regular immersion; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-ext-sheaf-negative: the existing statement concerns Koszul-regular immersion Ext sheaf negative-degree comparison (q < 0); it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-ext-sheaf-nonnegative: the existing statement concerns Koszul-regular immersion Ext sheaf nonnegative-degree comparison (0 ≤ q); it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-immersion-ext-sheaf: the existing statement concerns Cohomology sheaves of a Koszul-regular immersion; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-regular-sequence-dual-complex: the existing statement gives the derived dual and its conormal determinant and localization, not the signed equality with two successive coinduction counits or Tor-independent scalar naturality of that equality.

lem-sfb-koszul-evaluation-pasting vs lem-sc-koszul-roof-comparison-independence: the existing statement concerns Equal Koszul roofs give equal normalized conormal values; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-d3-koszul-normalized-projective-resolution: the existing statement concerns The Koszul projective resolution with its quotient augmentation; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-g3-affine-koszul-signed-dual-coefficient-square: the existing statement concerns Affine koszul signed dual coefficient square; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-j3-ext-signed-dual-homology: the existing statement concerns Ext is homology of a termwise identified signed dual resolution; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-j3-koszul-coefficient-top-homology: the existing statement concerns Top cohomology of algebraic Koszul coefficient reduction; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-j3-koszul-ext-coefficient-stalk-model: the existing statement concerns Commuting affine Koszul model for every Ext coefficient stalk; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-j3-koszul-projective-resolution: the existing statement concerns The Koszul chain complex is a projective resolution of its quotient; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-j3-koszul-quotient-coefficient-complex: the existing statement concerns Explicit quotient-valued Koszul dual complex and reduction morphism; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-k1-koszul-ext-coefficient-affine-model: the existing statement concerns Affine sheaf-level Koszul Ext coefficient square; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-lem-sc-koszul-coefficient-extension-chi: the existing statement concerns Coefficient extension cochain map; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-lem-sc-koszul-coefficient-extension-nu: the existing statement concerns Coefficient extension normal determinant map; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-q2-koszul-derived-top-evaluation: the existing statement concerns Equal derived Koszul maps have equal top evaluations modulo the ideal; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-q2-koszul-generator-chain-map: the existing statement gives a generator-substitution chain map, with no regularity or invertibility required; it does not state the derived evaluation-pasting or scalar-change equalities.

lem-sfb-koszul-evaluation-pasting vs new-s3-koszul-conormal-comparison-map: the existing statement concerns Construction of the normalized dual Koszul comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs new-s3-koszul-conormal-comparison-quasi-iso: the existing statement concerns Quasi-isomorphism of a normalized dual Koszul comparison; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-weil-pbc-koszul-last-generator-assembly: the existing statement concerns Explicit last-generator exterior-power assembly is bijective; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-weil-pbc-koszul-tensor-cone-coordinates: the existing statement concerns Tensor Koszul coordinates for adjoining the final generator; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs def-trf-lci-koszul-duality-data: the existing statement concerns Constant-codimension polynomial lci charts and signed Koszul normalization; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-trf-lci-adjunction-top-ext: the existing statement concerns Top Ext consequence of normalized derived Koszul adjunction; it does not identify the signed coinduction trace for two successive arbitrary Koszul-resolved quotient maps with the concatenated trace and its Tor-independent scalar extensions.

lem-sfb-koszul-evaluation-pasting vs lem-trf-lci-koszul-duality-determinant-comparison: the existing theorem identifies geometric polynomial lci duality with an intrinsic cotangent determinant and its refinements; the new statement gives coinduction trace pasting for arbitrary successive algebraic Koszul-resolved quotients and arbitrary Tor-independent scalar changes, with an explicit block sign. It is not a one-line specialization of the geometric chart statement.

lem-sfb-koszul-evaluation-pasting vs lem-trf-polynomial-graph-coinduction: the existing statement supplies a polynomial graph resolution and an oriented coinduction isomorphism, already cited in step 2; it gives neither successive-quotient trace pasting nor its signed scalar-change law for arbitrary Koszul-resolved quotients.

