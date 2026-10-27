# Q05 stage-1 delivery: lem-sfb-induced-dual-lowest-distribution-generator

## 1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-induced-dual-lowest-distribution-generator.json: statement, split into eight proof steps; not a Mathlib leaf.
- citations.json: verbatim cited statements for every (step, node) pair.
- report.md: this report. Search provenance is in searches.jsonl.

No new nodes and no new Mathlib leaves. Supporting scripts and the local extracted Milne text are sandbox research artifacts, not delivery files. No Lean file was written; no compiler, Lake, build, or local DAG/preflight checker was run. No repository or launcher file was modified.

## 2. Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id, lowest weight, Weyl module, hyperalgebra, Mathieu, and induced-dual terminology found no project declaration stating this item. The returned duality declarations concern sheaf duality, not induced algebraic-group representations.

## 3. Wanted literature

WANTED: Olivier Mathieu, Tilting modules and their applications (2000), Sections 1--2, printed pp.150--155, for the item. The PDF named by the live node is absent locally. I read the author-hosted https://www.imsc.res.in/~knr/vdk/mathieu.pdf online, especially Lemma 2.1 and the start of Lemma 2.3. No file was downloaded into the repository.

WANTED: Brion--Kumar, Frobenius Splitting Methods in Geometry and Representation Theory (2005), Section 2.1 and Exercise 2.2.E, for the existing Schubert-curve and fundamental-boundary inputs. I read the author-hosted https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf online, printed pp.61--64 (and the cited exercise through its existing node); no new node depends on a new source.

Locally read sources: Milne, Algebraic Groups iAG2017, the homogeneous quotient construction in 18c and the extracted passages 21.24, 22.22--22.27, 22.48--22.49; Stacks coherent.tex, Tag 02O6, lemma-proper-over-affine-cohomology-finite, and Tag 01XS, section-cohomology-projective-space, lemma-cohomology-projective-space-over-ring. Sources by tag are recorded for the two geometric cohomology steps.

## 4. Problems found and changes

The item had no proof and imported doubled TeX escapes. I normalized those escapes without changing its mathematical wording or hypotheses. Its source, created, chapter, unit, blueprint.from.node=null, and via chain are retained. `blueprint_refs.py ancestor` returns None for this inherited ancestry; this delivery does not invent an imported blueprint ancestor. The latest blueprint unit and direct-image proof were read. They place this input far below the existing alteration/geometric-reductivity/Kempf branch; this split changes no unit or chapter route.

Milne 22.48 and the adjoining dominance prose have conflicting sign conventions relative to the actual quotient action. I use the item's explicit semi-invariance equation and the already corrected homogeneous-line and fundamental-boundary node statements throughout. In particular V_eta consists of f with f(gb)=(-w_0 eta)(pi_T(b))f(g), and evaluation at n_0 has dual weight -eta. The item is mathematically consistent; no statement dispute or added restriction m_i<p is needed. I do not use the Weyl dimension formula, Kempf vanishing, irreducibility, or the restricted infinitesimal invariants theorem to establish its prerequisites, which would risk circularity.

The new searches returned abstract root-system representations and Lie-module generalized weights, with no rational algebraic-group induced module or distribution theorem. I read the returned signatures; Chain.lean's coroot-chain theorem explicitly assumes CharZero, so it cannot supply these positive-characteristic divided-power relations. A second semantic phrasing and LeanSearch were both run. No unavailable search was represented as a successful absence result.

## 5. Unfinished work

Nothing needed for this one-level split is left unstated. Existing supporting nodes remain independent queue items; I do not claim their natural-language statements are already formalized.

## Not duplicates

No new nodes were created. Whole-DAG statement searches found the existing fundamental-boundary, character-lattice, Bruhat-chart, root-parametrization, rank-one, Schubert-degree and projective-cohomology statements used here. They are reused directly. Whole imported-blueprint searches for Weyl, lowest weight and distribution found no matching blueprint theorem; the latest blueprint text was also searched. There is no new node that restates the item or one of its clauses.

## Review by Q05

I read delivery-errors B--E, both occurrences, against the actual node statements and the sources. The proof is an assembly of existing geometric inputs with the coefficient argument written out, rather than a citation to a renamed cyclicity theorem. Every step is under 2000 characters. No hidden comparison is justified by saying only that it transports: the root-coordinate change, matrix coefficient, homogeneous-line frame, coroot pairing and coefficient extraction are all displayed.

Step 1 uses rho-regular-weyl-orbit for the positive-to-negative longest element and its involution; reductive-rank-one-reflections for equivariance of coroots under normalizer conjugation; simply-connected-character-lattice for integral fundamental characters; fundamental-flag-boundary-sections for actual sections nonvanishing at n_0B; and homogeneous-line-bundle-sections for regular functions and their character product. I verified each of those clauses in its statement. Semisimple simply connected S and algebraically closed F meet all their hypotheses; positivity makes the exponents nonnegative. Their product is explicitly a nonzero section of exactly M_(-w_0 eta), with no use of a higher vanishing theorem. Normalization makes its evaluation nonzero, including zero coefficients and an empty root system.

Step 2 uses reductive-borel-pair-structure for proper Q, homogeneous-line-bundle-sections for coherence and the rational left action, and coherent-hi for finite H^0 over a Noetherian affine base. Those statements give exactly the three inputs: the base is Spec F, its ring is Noetherian, and the sheaf is coherent. Nonzero is provided by the constructed product, not assumed from finiteness. The contragredient rational structure is the elementary inverse-matrix construction.

Step 3 uses the stated homogeneous-section action and w_0^2=1 to compute the actual character -eta of the evaluation functional. The equation is over arbitrary F-algebras; it is not merely a claim about F-points or infinitesimal weights.

Step 4 uses bruhat-longest-cell-charts for both integral S and the dense open U times B, and for U being affine space; homogeneous-line-bundle-sections gives the trivialization and action formula. Vanishing on that open implies zero by domain localization. This is a short restriction argument, not an extra uncited theorem about distributions. Translating affine coordinates puts the identity at the origin. The calculation (uw)(v)=f_v(un_0) fixes the inverse convention before any distribution is applied.

Step 5 uses only steps 2 and 4, the distribution definition in the item, coefficient extraction on polynomials, and finite-dimensional linear algebra. A monomial coefficient annihilates the required power of the augmentation ideal; hence it is an actual distribution. All coefficients, not only derivatives of order below p, annihilate P_v, so P_v vanishes. A basis extension explicitly gives the annihilating vector that would exist if Hw were proper. This is why cyclicity is valid without a restricted-weight assumption and why no new distribution-detection lemma is needed.

Step 6 cites root-subgroup-parametrizations for uniqueness of the root group with the transformed tangent weight, reductive-rank-one-reflections for the SL2 map and Weyl/coroot action, and homogeneous-line-schubert-curve-degree for the actual SL2/B2 curve and first-column parametrization. I checked that the last statement gives an isomorphism with P1, not merely a numerical degree. The lower root map is obtained from the upper one by the displayed SL2 Weyl matrix; its coordinate change is ct because it is an isomorphism of affine lines fixing zero. Thus the curve is the translated R_j for j with alpha_j=-w_0 alpha_i, which is essential for getting m_i rather than an incorrectly indexed degree.

Step 7 cites homogeneous-line-bundle-sections for its left linearization, Schubert-curve-degree for the isomorphism with O(d), reductive-rank-one-reflections for normalizer invariance of the coroot pairing, and projective-space-twist-cohomology for the actual monomial basis. I checked these statements separately; none is being used just from its proof. The quotient frame along the root chart and the standard O(m_i) frame differ by a unit in F[t], so by a constant. Therefore the function whose coefficient defines D_i^(n) has the polynomial degree bound in that very frame. This supplies the annihilation statement without division by n!, even when m_i>=p. The rank-one calculation works for arbitrary parametrizations x_i since scaling t preserves the bound.

Step 8 evaluates the trivial-group definitions directly. I also tested S=SL2, eta=m omega, in characteristic 2 with m=0, 1, 2, and general m>=p: V_eta is the degree-m section space on P1; w evaluates at the opposite flag; the full coefficient distributions recover every monomial coefficient although ordinary derivatives do not. For a product of rank-one factors the chart polynomials and simple-root degree bounds separate by factors. These tests confirm the signs, use of the full distribution algebra, and the unrestricted m_i clause.

I checked the cited dependency closures for a return path to the item: none of the chosen geometric prerequisites depends on it. The two cross-unit inputs coherent-hi and projective-space-twist-cohomology are declared in split_report.tool_uses as generic tools, not a replacement of the current unit's route. The citation file copies each cited statement verbatim, preserving all clauses used rather than bending a short quote into a stronger theorem. No new-node format, search provenance, duplicate-tag or Mathlib-leaf issue arises because the delivery creates no node.

## Dry-run repair

The first server preflight rejected TeX matrix row separators in step 6 as doubled backslashes (B4). I replaced the two matrix displays by the explicit entries of J and by I+zE_21. The rank-one calculation is identical; the serialized proof now contains no doubled-backslash text.
