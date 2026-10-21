# Stage-1 report: lem-pur-supported-hom-cocycle-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-supported-hom-cocycle-normalization.json`: statement node, now split into ten steps. Statement preserved verbatim. No exact Mathlib match: the ordinary Ext cocycle and constant-sheaf section comparisons found by the searches do not give the closed-support presentation or its geometric normalization.
- No new DAG nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node pair. Quotations include the full cited statements so that their hypotheses remain visible.
- `searches.jsonl`: the five searches actually run for this item, including the second semantic phrasing. All services answered; original inherited searches remain in the node. `write_split.py` is a sandbox-only drafting script, not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for supported-Hom/cocycle/evaluation terminology. Read the nearby `SixFunctors/OpenClosed/SupportedSections.lean` and `SixFunctors/Etale/Derived/ClosedImmersionUpperShriek.lean`. They give sheaf-level support adjunctions, not the full evaluation and arbitrary-integer, arbitrary-resolution normalization in this item. No Lean was written and no compiler was run.

## WANTED

None. The sources needed here are present.

## Corrections and scope

The imported item had no proof. Its statement is unchanged, including both topologies, actual restriction maps, all integer degrees, lack of quasi-compactness, and agreement with the etale restriction cone. The proof is marked agent-written: Milne supplies the underived evaluation/Ext argument, while this split makes the module-valued, pro-etale and bounded-below normalization explicit using existing DAG results.

I used the current blueprint under `main-20261015/blueprint/sec-six-functors-basics/`, where the relevant files now live, and read the chapter and unit records (`sec-smooth-purity`, `sk-prop-a1-kummer`). This is a comparison tool for the supported Cartier boundary in the affine-line orientation proof, through the existing supported-Hom-pullback parent. It does not alter the chapter or unit route. It uses no SGA source and no purity theorem.

Two possible gaps were addressed before submission. First, I did not infer that forgetting a module-sheaf action preserves injectives; this need not hold. The proof derives functors on the module-sheaf category with values in abelian groups. Second, agreement of a cone map cannot be inferred just from its composite to the source. Step 10 computes the actual canonical comparison component as `(0, (f rho)(1))`, identifying it with the specified kernel-cone map. I also explicitly cited exact inverse image and constant-ring pullback, rather than silently assuming that the restriction of the injective resolution is a resolution.

## Not duplicates

No new nodes were created. The DAG and whole-blueprint searches for `supported`, `supported-hom`, `closed-support-hom`, and `cocycle-normalization` found the existing supported-Hom lemmas. They give the isomorphisms and tools, whereas this item fixes their evaluation and roof normalization. In particular the pro-etale presentation, both open adjunctions, bounded-below K-injectivity, right-derived functor computation, and kernel-to-cone comparison already have nodes. I cited them rather than creating special cases or clauses of this item as new nodes.

## Review by Q16

I read Milne, *Lectures on Etale Cohomology*, PDF pages 66--67: Example 9.5 evaluates at 1, and the Ext proof of Theorem 9.4 uses the constant open-closed sequence and open adjunction. I read the current blueprint proofs of `lem-pur-supported-hom`, `lem-amb-closed-support-hom`, and `thm-pur-affine-line-orientation`, as well as the existing DAG splits. I read Stacks `etale-cohomology.tex`, Tag 095L / `lemma-ses-associated-to-open`; `sites-modules.tex`, the formula `equation-map-lower-shriek-OU-into-module` and Tag 03DJ / `lemma-extension-by-zero-exact`; and `derived.tex`, Tags 05TH, 05TI, 070I, 070J. The adaptations are explicitly attributed to the agent. There are no new nodes whose sources need a separate review.

For step 1 I opened both cited statements: `lem-pur-ringed-site-grothendieck-abelian` applies to any small ringed site, and `lem-sp-grothendieck-enough-injectives` supplies enough injectives. The prescribed small representatives and the constant sheaf of commutative rings meet their hypotheses in each topology.

For step 2, `def-weil-sheaf-of-modules-category` really specifies linear components and semilinear restriction, and `def-weil-pbc-constant-sheaf` gives the constant coefficient ring. Multiplication by the restriction of a section defines the inverse evaluation map directly for arbitrary local scalars; no unstated connectedness or global-constant-sections assertion is involved.

For step 3, I checked the statements of both open adjunction nodes. The etale statement specifies its counit on localized objects, and the pro-etale statement is the adjunction to restriction. Naturality of the adjunction bijection and the counit identity give the adjunct of `g epsilon`; its value at 1 is explicitly the restriction of `g(1)`. This is an elementary adjunction calculation, rather than an additional geometric comparison theorem.

For step 4, the etale short-exact-sequence statement specifies both adjunction maps and includes commutative-ring module sheaves. `prop-weil-pbc-inverse-image-modules-exact` supplies the canonical constant-ring identification, so the closed unit is the stipulated rho. The pro-etale presentation statement specifies this same rho and explicitly says it is the cokernel of the open counit without quasi-compactness. The argument uses only this cokernel on the pro-etale site, not an unproved monomorphism there. The universal property constructs the required unique map from a supported section, and proves naturality and additivity by equality after precomposition with rho.

Step 5 uses only the supported-section definition and the cochain convention. The differential equation is written out, including its effect on boundaries. For step 6, I opened the full statement of `lem-weil-pbc-right-derived-plus-injective`: its clause (1) is the universal property needed to derive the natural transformation, and clause (2) says the derived unit is invertible on every bounded-below injective complex. Both inverse and resolution-comparison equalities follow from those clauses; I did not use any unspecified choice of a derived isomorphism.

For step 7, the bounded-below K-injective node covers precisely the stipulated resolution. The statement of `lem-sc-p1-rhom-hom-derived-roof` covers an arbitrary object P, arbitrary bounded-below complex, every integer a, and the exact derived-unit transports used here. Its displayed inverse-resolution roof is the required one. No finite-Tor or constructibility hypothesis is among its assumptions. Step 8 uses the naturality clause of that same statement and the canonical derived construction from step 6. Thus independence is proved for the actual maps on cohomology, not by selecting resolution-dependent isomorphisms.

For step 9, I reopened all six cited statements. The etale short-exact sequence makes epsilon monic, the definition of injectivity gives extension across this monomorphism, exactness of etale extension by zero and its adjunction give injectivity after open restriction by the explicit lifting argument, and exact inverse image preserves the resolution quasi-isomorphism. Finally the right-derived computation lemma applies to both bounded-below injective complexes. This establishes degreewise surjectivity of the actual restriction before using the kernel-cone lemma.

For step 10, the kernel-cone node specifies both the degreewise-epimorphism hypothesis and the exact comparison `(0, inclusion)` with its differential. Step 9 meets the hypothesis. I checked the source construction of the closed-support-Hom cone: applying Hom to the fixed short exact sequence realizes its canonical triangle by that very comparison, whose component is explicitly calculated in the step. The roof node then gives the same derived morphism. This also checks the shifted-cone sign. The use of `lem-amb-closed-support-hom` is for its stated cone isomorphism, not for an unstated lemma in its proof; the normalization is established here by the explicit map.

I tested empty Z (P and supported sections vanish), Z=X (rho is the identity, recovering evaluation and ordinary derived Hom), empty X, zero M and zero F, a supported cocycle that is a boundary, a=0, and negative a with a resolution bounded below. In particular the morphism into I[a] has sole component f_s and the cocycle condition is unaffected by the shift sign. A non-quasi-compact open complement is allowed: the pro-etale presentation explicitly permits it, and the etale exactness and extension-by-zero assertions have no quasi-compactness hypothesis. None of the steps assumes geometric stalk conservativity on the pro-etale site.

Every new fact in the argument is either supplied by a cited statement or written as a direct evaluation, cokernel, or naturality calculation. I checked delivery-errors B--E: no new elementary/duplicate/restatement nodes, no missing source tags, no citations of a mere definition for an existence result, no added hypotheses, no circular reliance on the pullback parent, and no long non-elementary step over 2000 characters. The statement and inherited blueprint/import metadata are retained.

## Generic tools outside the unit

The following existing nodes are used only as generic tools, not as an alternative route through other geometric units. If route bookkeeping requires additional `tool_uses`, that is for the maintainer; I have not written that field: `lem-sp-grothendieck-enough-injectives`, `lem-weil-pbc-extension-by-zero-adjunction`, `lem-weil-pbc-open-closed-short-exact`, `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-right-derived-plus-injective`, `lem-weil-pbc-bounded-below-injectives-kinjective`, `lem-sc-p1-rhom-hom-derived-roof`, `lem-weil-pbc-extension-by-zero-exact`, and `lem-weil-degreewise-epi-kernel-cocone-qis`. These are the ordinary homological and open-localization tools needed to fix this comparison. The other cited purity nodes belong to the same chapter/route or supply its notions.

## Unfinished work

None in this one-level split. The existing unsplit dependencies remain their own items. Delivery verification is recorded by the required dry run and push output.
