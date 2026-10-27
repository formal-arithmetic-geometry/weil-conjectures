# Stage-1 report: lem-per-separable-regular-affinoid-residual-conormal

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-separable-regular-affinoid-residual-conormal.json`: item, split, statement unchanged, no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-tate-separable-local-cotangent-coordinates.json`: one new statement-only unsplit node, no Mathlib match.
- `citations.json`: verbatim statement extracts for every proof-step citation.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, affinoid, Tate algebra, restricted series and residual conormal gave no declaration stating the item or the new ambient-coordinate input. The two hits mentioning a Tate algebra in Koszul files mean a different, graded algebra.

## WANTED

WANTED: Conrad, Several approaches to non-archimedean geometry, https://math.stanford.edu/~conrad/papers/aws.pdf, Theorem 1.1.5(1), PDF p.4, and Exercise 1.2.8(4), for the ambient Tate local ring. Read online; no archival copy was found in the named literature directory.

WANTED: Conrad, Irreducible components of rigid spaces, https://www.numdam.org/article/AIF_1999__49_2_473_0.pdf, section 1.1 printed p.477 and proof of Lemma 3.3.1 printed p.510, for completion comparison and separable-point cotangent coordinates. Read online. Only sandbox files were written, so the wanted request is here rather than in literature/LIST.md.

The original Temkin Excellent_Desingularization.pdf request remains outstanding; this split does not pretend to have read that PDF. Its original source field is retained. The proof_origin is agent because the actual assembly and first-order refinement are supplied by the worker.

## What was wrong or incomplete

The item was statement-only. Its assertion is correct, but replacing separable residue by arbitrary residue or replacing analytic differentials by ordinary algebraic Kahler differentials would invalidate this argument. I kept all hypotheses and conclusions unchanged. I did not infer geometric regularity of B from its local regularity.

The new input is about the ambient Tate algebra alone: it has no ideal I, quotient B, or conormal map. Therefore it does not restate the item or transfer the item's main regular-quotient argument into a new node. Regularity of the quotient is used only in the item, through the already existing Tag 00NR node.

## Review by Q61

I read the worker brief, stage-1 contract, B through E of both delivery-error lists, GOAL, the chapter and unit records, the current blueprint ancestor statement and proof, and the current item. There was no earlier sandbox split or report and no repair note. The item is a descendant supporting the inherited formal-algebraization branch of the ancestor's Step 3. This delivery does not change the chapter, unit statement, realization fields or proof route.

For the analytic source I read Conrad's AWS Theorem 1.1.5(1), which states Noetherian regularity of the Tate algebra and dimension r of its local rings at maximal ideals. I also read the 1999 paper's printed p.477, where affinoid algebraic localization and analytic stalk have canonically identical completions, and p.510, which explains the completed power-series description at a regular point with finite separable residue. The ambient-coordinate statement is an agent-formulated first-order refinement, not a literal quotation of either theorem. One way to justify it at its future split is to pass to a finite separable splitting extension of the residue field, use rational Taylor coordinates, and descend the cotangent map along the resulting finite etale local map. This uses separability only for the ambient local map; no regularity of any coefficient-extended quotient is needed. That future proof is not embedded in the new node's statement.

Step 1 is the coefficient calculation. The shift of exponents is injective and |n| is at most one in every nonarchimedean characteristic, so differentiation preserves restrictedness. Each coefficient of a product is a finite convolution, proving Leibniz without differentiating an unproved analytic limit. Because I is contained in n, both Leibniz terms for a product in nI vanish in the residue field. This checks descent and scalar linearity explicitly.

Step 2 uses the new ambient node for exactly regularity of R, its residue map and the displayed cotangent isomorphism. I checked completeness, nontriviality, maximality, and finite separability against its full statement. The quotient-localization node is used with the original ring T, ideal I, and the prime m in B; its explicit isomorphism identifies R/J with the given B_m, which is regular by hypothesis. I read that node's whole statement and Stacks algebra.tex Tag 00CT, proposition-localize-quotient. This does not assume B is regular away from m.

Step 3 cites the localization definition for its fraction equivalence. I read that full statement. I wrote both directions of the residual-ideal identification, including annihilating a fraction equality by v outside n. Surjectivity uses a lift of the inverse residue of a denominator; injectivity uses a lift of the inverse residue of vu. This avoids assuming T is a domain or that I localizes injectively. The equality pJ=(nI)R is expansion of finite products and finite sums of fractions, not an appeal to flatness.

Step 4 cites exactly lem-weil-pbc-regular-local-quotient-independent-generators. I read its statement and the local Stacks proof, algebra.tex lemma-regular-quotient-regular, Tag 00NR. It supplies generators independent in p/p², exactly what is needed; a definition of regularity would not supply this theorem. Both local rings required by that node were proved regular in Step 2, and J is contained in p. This is a generic commutative-algebra tool in another unit, declared in split_report.tool_uses together with the generic quotient-localization identity.

Step 5 is the actual conormal injectivity argument: expand an element in the independent generators, then reduce its coefficients modulo p. A zero tangent class forces every coefficient into p, giving membership in pJ. It invokes only Step 4, not a new hidden theorem. Step 6 checks the composite on every representative g, using the new node's formula with denominator 1. Thus the original derivative map is precisely theta beta alpha. Every cited formula was copied verbatim into citations.json and checked as a substring of the cited statement; the coordinate formula, not merely existence of an unnamed isomorphism, is used in Step 6.

I checked B1--B10: the new node is self-contained, statement-only, has definitions cited, actual recorded searches, source places and full blueprint ancestry. It is not a Mathlib leaf. For C1--C8 every non-elementary input is cited by statement, no proof of a cited node is used, and no descendant of the item is cited. For D1--D5 the quotient regularity and independent-generator kernel argument stay in the item, rather than moving into an equivalent lemma. For E1--E7 all required hypotheses and all fraction denominators are explicit, and the coordinate composite is checked on representatives. No proof step exceeds 2000 characters.

I checked small cases: r=0 forces T=F, n=I=0; s=0 and I=0 give zero source. At a rational point the new ambient node specializes to the existing rational-coordinate node. At a genuinely separable nonrational point in one variable, the class of its minimal polynomial maps to its nonzero derivative. Separability cannot be removed: for F=F_p((t)) and n=(x^p-t), the quotient is a field and hence regular, but the nonzero class of x^p-t in n/n² has derivative zero. The assumption in the delivered item excludes exactly that example.

Mathlib searches were run with the supplied msearch command and their actual results read. I inspected the entire MvPowerSeries/Restricted.lean: it constructs restricted series and their subring but proves no regular local or cotangent theorem. Smooth/Local.lean:34--55 concerns ordinary algebraic formal smoothness, not continuous Tate differentials. Kaehler/JacobiZariski.lean:148 compares polynomial generator presentations. LeanFinder's generic cotangent-space results and power-series residue-field/Weierstrass results do not give the new input. A second phrasing was used for both the item and the ambient node; the exact query records are retained in searches.jsonl and in the respective nodes.

## Not duplicates

lem-per-tate-separable-local-cotangent-coordinates vs lem-per-tate-rational-local-coordinates: the existing node assumes the residue point is F-rational and supplies rational Taylor coordinates; the new node allows every finite separable residue extension and needs the cotangent comparison at that nonrational point. The new statement is not a specialization of the old one over the original field.

lem-per-tate-separable-local-cotangent-coordinates vs lem-trf-affinoid-polynomial-closed-point-comparison: the existing node identifies completed local rings with polynomial ones; it does not state regularity or the termwise derivative identification of p/p² with kappa^r.

lem-per-tate-separable-local-cotangent-coordinates vs lem-per-affinoid-residual-conormal-injective: that node concerns the relation ideal of a geometrically regular quotient; the new node has no quotient or relation ideal and only describes the ambient maximal ideal modulo its square.

lem-per-tate-separable-local-cotangent-coordinates vs lem-per-tate-maximal-residue-evaluation: that node supplies residue-field norms and evaluation, not local regularity or cotangent coordinates.

Whole-DAG statement searches for Tate algebras, restricted series and cotangent coordinates, plus blueprint_refs.py searches for restricted series, cotangent space, Tate and separable residue, found no blueprint node stating the new input. The many blueprint hits for 'Tate' concern Tate twists rather than this local-algebra assertion.

## Unfinished work

No unresolved part of the item's assembly proof. The new analytic ambient-coordinate node is intentionally unsplit and will need its own stage-1 work. All other cited nodes already exist. Validation and push results are supplied by the required delivery command.
