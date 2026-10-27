# Worker report

1. Files written:
   - dag/nodes/sec-trace-formula/lem-trf-affinoid-supremum-seminorm-calculus.json: item, split, unchanged statement; not a Mathlib leaf.
   - dag/nodes/sec-trace-formula/lem-trf-tate-unit-coefficient-criterion.json: one new statement-only unsplit node; no Mathlib match.
   - citations.json: complete verbatim statements for all eight citation pairs.
   - searches.jsonl: actual msearch.py query/result records; all services answered.
2. Attachments: none. Searched lean/WeilConjectures for the item tag, affinoid, seminorm, Gauss and restricted-series terminology. No project declaration supplies the item. No Lean written or compiled.
3. WANTED: Bosch, Lectures on Formal and Rigid Geometry (April 2008), https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, Section 1.2 Corollary 4 (printed p.10), Section 1.2 Corollary 11 (p.14), Section 1.4 Propositions 5-8 (pp.23-24), and Appendix finite-extension absolute values, for the item and the new unit-criterion node. The primary PDF was read online. The named archival copy is absent locally; no download was made.
4. The item statement is correct and unchanged. Its source reference to pp.23-24 is right (PDF pp.24-25). The title says seminorm although its listed clauses are not all seminorm axioms; step 3 also verifies those axioms directly. The definition node for affinoid quotient presentations imposes a topology; the item's own inline algebraic quotient definition is the one used here, so continuity is not added to its homomorphism hypothesis. The current latest blueprint uses contracting correspondences for the curve unit; the old analytic normalization branch is historical support below node level. I retained its recorded ancestry and did not replace any unit step. The original item had no proof.
5. Nothing in this split remains unfinished. The new theorem is intentionally statement-only for a later stage-1 item. Delivery pending the prescribed checks.

## Sources and proof design

I read the current chapter record, unit sk-i-curve-zero, latest unit statement and lem-trf-local-term-locality.proof.md; the analytic material is an inherited historical ingredient, not a substitute for that route. I read Bosch Section 1.2's Gauss norm, completeness, unit criterion and maximum-principle paragraphs and Section 1.4's definition and Propositions 5-8. Bosch obtains the Gauss lower bound by a point over the algebraic closure. I give instead the explicit auxiliary hypersurface 1-Yg=0, whose properness follows from Corollary 4. This avoids silently using a new theorem about residue-field lifting to an algebraic closure. Because the source is not archived locally and this lower-bound argument differs, proof_origin is honestly agent-written.

For a future split of the new node: Bosch proves Gauss multiplicativity by reducing normalized series modulo elements of absolute value less than one; the reduction ring is a polynomial ring over the residue field, hence a domain. If f and its inverse have norm one, both reduce and the reductions are inverse polynomials, hence constants. Conversely strict dominance gives f=c_0(1-h) with norm(h)<1 and inverse c_0^{-1} sum h^n. This argument is report material, not a hidden proof in the new statement. The actual new node contains no proof steps or dependencies of a proof.

## Not duplicates

lem-trf-tate-unit-coefficient-criterion vs lem-trf-affinoid-supremum-seminorm-calculus: invertibility of a restricted series is an algebraic criterion; none of the item's conclusions asserts it. The item actually derives its Gauss comparison using 1-Yg rather than applying a restated comparison clause.

lem-trf-tate-unit-coefficient-criterion vs lem-trf-restricted-series-gauss-completion: the latter states submultiplicativity, completeness, truncations and regrouping, but no unit criterion or Gauss multiplicativity.

lem-trf-tate-unit-coefficient-criterion vs lem-trf-tate-weierstrass-norm-division: division and preparation with a distinguished variable do not state the arbitrary multivariate unit criterion. Neither is cited for a claim absent from its statement.

lem-trf-tate-unit-coefficient-criterion vs lem-per-tate-maximal-residue-evaluation: the latter gives finite residue fields and their coordinate/evaluation description, not which series are invertible. It is reused, not recreated.

DAG searches by Gauss/unit/constant-coefficient terminology and a parsed whole-DAG statement scan found no existing criterion. blueprint_refs.py searches for Gauss norm, Tate algebra unit and invertible restricted found no equivalent blueprint node; broad constant-coefficient results concern different notions. The new node has no Stacks tag, since Bosch supplies the analytic theorem. The existing maximal-ideal-existence node is the Mathlib leaf for Stacks 00E0, label lemma-Zariski-topology; I read its statement and the corresponding algebra.tex source and reused it.

## Mathlib searches

The item and the new node were each searched with leanfinder (two phrasings), loogle, leansearch and grep, all through the required msearch.py. Exact query text and returned summaries are preserved in each node and searches.jsonl. I read MvPowerSeries/Inverse.lean:138, Restricted.lean, MvPowerSeries/GaussNorm.lean, SpectralNorm.lean:628-641 and IsPowMulFaithful.lean:37-66. Formal-series inverses need not remain restricted: 1-X is a formal unit, but not a Tate unit. Thus isUnit_iff_constantCoeff is not a match. The spectralNorm declarations concern algebraic field extensions; they do not identify a maximal-ideal supremum on arbitrary quotients. Generic contraction assumes boundedness and does not prove the needed evaluation theorem. Restricted-product units refer to another ring. No new Mathlib leaf is claimed.

## Review by NC

I checked B-E against the actual files and the Bosch pages, not merely the field schema. The item introduces exactly the nonzero affinoid quotients needed. The new criterion introduces K, all series, their norm and invertibility, includes r=0, and cites the field and restricted-series definition nodes; its statement has no proof sketch. Its ancestry is the item's existing blueprint chain with the item prefixed to via; same_as is empty after searching. The sources are analytic Bosch references rather than invented Stacks tags. Every proof step has fewer than 1000 characters, so none hides a long inline standard lemma.

Step 1 uses the full statement of lem-per-tate-maximal-residue-evaluation for finiteness, uniqueness and completeness; the inverse-image quotient is a K-isomorphism, so transport is legitimate. The maximal-ideal-existence leaf applies because A is explicitly nonzero. I opened that node and verified that it gives a maximal ideal for every proper ideal, not just a nonempty prime spectrum.

Step 2 uses the same residue node for the coordinate bounds and convergent evaluation formula, and lem-per-tate-banach-substitution for the contractive norm estimate. A finite residue field with its extending absolute value is a complete commutative normed K-algebra with norm(1)=1 and scalar compatibility, so every hypothesis of substitution holds. Supremum existence is then ordinary completeness of the real numbers for a bounded nonempty set. I do not assume continuity of an arbitrary algebraic presentation.

Steps 3 and 4 are elementary consequences of that pointwise bound and the field absolute-value axioms. In particular the infimum is over a nonempty set bounded below. For powers I checked both inequalities, including the s=0 case; the reverse one uses a number u strictly below s rather than assuming a maximizing ideal exists. Nilpotents map to zero in every field quotient.

Step 5 is the explicit proof of Bosch Proposition 6: an image subalgebra of a finite field extension is finite-dimensional, and its injective multiplication operators are surjective. This proves the contracted ideal is maximal before invoking uniqueness from step 1. No finite-type or continuity hypothesis on psi is smuggled in, and no general theorem about arbitrary maximal-ideal contraction is used.

Step 6 uses the new unit criterion precisely in its negated direction: h has constant coefficient 1 and tail norm 1, hence is not invertible. The principal ideal is proper exactly because h is not invertible. The existing maximal-ideal leaf then produces M. Choosing a largest coefficient of f is justified by the coefficients tending to zero and a finite maximum, with zero f handled separately. This constructs the norm-attaining point rather than hiding a separate maximum-modulus theorem.

Step 7 again uses the actual residue-evaluation and substitution statements. The full (d+1)-tuple has absolute values at most one; the evaluation of g uses only its first d coordinates, and the explicit convergent-sum formula identifies it with the residue of the same series in the larger ring. From y*g(x)=1 and both bounds one gets equality. The image is a field by the finite-dimensional argument written in step 5, so ker(e) is maximal in T_d, not merely prime. Restriction of the absolute value agrees by uniqueness. This establishes the lower bound without a surjectivity claim about arbitrary maps of maximal spectra.

Edge cases: d=r=0 gives K itself and uses the auxiliary variable Y only when necessary. Zero series gives zero on both sides. Constants and monomials give the expected Gauss values. Over Q_p the residue field is finite, so K-rational unit-disc points alone would not suffice; the proof allows finite residue extensions throughout. The dual numbers K[epsilon]/(epsilon^2) give rho(epsilon)=0, confirming no reducedness has entered. The unit criterion gives units for 1+pX over Q_p and nonunits for 1-X and X, distinguishing it from the formal-series theorem. Noninjective psi causes no problem because its residue map factors through B/n. No forbidden SGA source, compiler, repository write, direct git command, launcher modification or subagent was used.

## Validation

The prescribed deliver.py --no-push invocation exited successfully and printed OK (not pushed) at c21f8e6b7da; server preflight passed. This supersedes the pending-validation note above. The push invocation below reruns the delivery gates on the final report.
