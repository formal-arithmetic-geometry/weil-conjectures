## Worker report

Q02, stage 1, 2026-10-22. Item: lem-sfb-local-surface-maximal-blowup-geometry.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-surface-maximal-blowup-geometry.json: the existing statement is unchanged; its previously empty proof is replaced by nine steps, using only existing nodes. Status is split. Earlier search records and provenance are retained, and five newly logged searches are appended.
- citations.json: one verbatim statement quotation for every cited node in every step.
- report.md: this report and the signed review below.

There are **0 new nodes and 0 new Mathlib leaves**. The sandbox also contains the actual searches.jsonl and the local write_split.py preparation script; neither is a project-source change.

### Attachments

None. Searches in lean/WeilConjectures by the exact blueprint tag and by maximal-ideal blowup, regular blowup and exceptional-divisor terminology found no declaration proving this statement. The nearby regular-local-surface depth-two flatness declarations concern a different statement. Mathlib declarations are supporting leaves, not project attachments.

### WANTED

None. The proof uses available Stacks sources.

### What was wrong or incomplete

The item had a correct statement but no proof. Its source sentence about closed-point dimension needed the actual local calculation, not just an invocation of regularity. Step 9 now uses maximal localizations of the polynomial ring and the nonzerodivisor quotient dimension formula explicitly. The reference statement and all its hypotheses are retained.

The imported provenance has blueprint.from.node = null; blueprint_refs.py ancestor reports None. I retained the existing from.place and via chain, which already pinpoint the rational-exceptional-curve argument in the parent. I read the current main-20261015 file sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This local surface calculation serves its alteration-route descendants rather than asserting that paragraph itself contains a surface-blowup proof. Searches of the whole imported blueprint for 0AGQ, 0AGR, regular local surface, blowup regular, and blowup found no imported node stating this item.

The whole-DAG search found lem-per-local-surface-maximal-blowup-geometry, an exact duplicate of this item's statement, also unsplit. I did not modify another worker's node or replace the argument with a citation to that duplicate. The maintainer can merge the two records after reviewing this proof. The existing split lem-per-surface-point-blowup-geometry contains the relevant chart argument but assumes a global integral excellent surface with an ample sheaf; it cannot be applied to arbitrary A here. Its supporting nodes can and do apply without those extra hypotheses.

### What remains unfinished

Nothing in the requested one-level split. The existing dependencies remain subject to their own recorded stage states; this delivery does not assert Lean completion of the item.

## Not duplicates

No new node was created. lem-sfb-local-surface-maximal-blowup-geometry vs lem-per-local-surface-maximal-blowup-geometry: their statements are identical, including the closed-point dimension assertion; this is an existing duplicate for maintainer consolidation, not a new proposed lemma. lem-sfb-local-surface-maximal-blowup-geometry vs lem-per-surface-point-blowup-geometry: the latter assumes an integral regular excellent global surface of dimension two with an ample sheaf and proves additional global geometry, whereas the present local-ring statement has no excellence or ampleness hypothesis.

## Review by Q02

I read resolve.tex, Tag 0AGQ (lemma-blowup) and Tag 0AGR (lemma-blowup-regular), including their proofs. The local ring is regular, Noetherian and of dimension two, its residue field is arbitrary, and the centre is the reduced closed point. Those are exactly the hypotheses in the item. The effective Cartier fibre, projective-line identification and regularity agree with these sources. The dimension-two assertion at closed points is their local-equation calculation completed with algebra.tex Tags 00OP (lemma-dim-affine-space) and 00KW (lemma-one-equation). I also read algebra.tex Tag 00NU (lemma-regular-mod-x) and more-algebra.tex Tag 0BIQ (lemma-blowup-regular-sequence). No SGA source is used.

For step 1 I opened the statements of def-nagata-global-blowup, its glue-data and local-model definitions, def-weil-regular-scheme, lem-weil-pbc-regular-local-generators-regular-sequence, prop-nagata-affine-blowup-chart-cover and lem-trf-blowup-chart-regular-sequence-presentation. Choosing the singleton affine cover uses the stated construction, not an unproved general base-change comparison. The generator lemma explicitly allows both orders of the two parameters, which is necessary to apply the chart-presentation theorem twice. The chart-cover theorem supplies a genuine finite open cover; the presentation theorem supplies the ring isomorphisms and the coordinate ratios. I verified the hypotheses before introducing either chart.

Step 2 uses the chart-ring definition for its actual subalgebra inclusion into A_x, and the effective-Cartier-ideal definition for the required nonzerodivisor condition. It does not infer injectivity from a picture of a blowup: the multiplication argument inside A_x is written out. The fibre-ring clause of def-weil-pbc-localization-at-prime supplies the tensor/quotient description; because the base ring is local at its maximal ideal, all the base localization denominators are already units. The equations y=xt and x=yu therefore compute the scheme-theoretic extended ideal and fibre, rather than merely the underlying set.

For step 3 I checked lem-weil-pbc-finite-type-algebra-noetherian: it applies to any finite-type algebra over any Noetherian ring, and both displayed quotient presentations satisfy it. Regular localness supplies Noetherianity of A. The definition pqf-def-locnoeth then applies to the actual affine cover. I also opened lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact: it states both the unit-ideal criterion for a basic-open cover and quasi-compactness of every affine spectrum. Step 3 cites it explicitly and writes the finite-expression argument, then takes the union of the two finite subcovers. This closes the general finiteness input rather than treating quasi-compactness of a spectrum as part of its definition.

For step 4 I opened def-nagata-affine-blowup-chart-map and def-nagata-affine-proj. Their degree-zero fractions specify the actual chart-coordinate maps and local structure sheaves. The intersection is exactly where the other homogeneous generator, hence its ratio, is invertible; the identity tu=1 is an identity of fractions. Reducing the explicit quotient presentations gives k[t] and k[u]. This elementary calculation is not a new lemma and does not assume that A contains a coefficient field.

Step 5 uses lem-weil-pbc-projective-space-standard-charts, including its two-coordinate case, the affine polynomial-ring description and the generators of O(1) on the charts. Thus it really supplies the projective line with the same inverse-coordinate transition computed in step 4. The chart maps and their inverses agree on the overlap, which is why they glue to a scheme isomorphism. I checked the statement of lem-sc-p1-polynomial-regular: it asserts regularity of every prime localization, not just the rational points or closed points. The affine-open stalk-localization theorem then gives all the local rings of E used later. The definition of regular scheme states the required equivalence with locally Noetherian schemes having regular local stalks.

For step 6 the affine-open stalk theorem supplies C_p, and lem-weil-pbc-localization-noetherian supplies its Noetherianity. The localization definition supplies fractions and their zero test. The preservation of the nonzerodivisor and the quotient-localization identification are written directly with those fractions; neither is taken from a definition that only names the corresponding notion. The hypothesis q in E is exactly what puts g in p and hence in the maximal ideal of the local ring.

For step 7 I checked the full statement of lem-exc-regular-local-lift-regular-sequence-quotient against R and the singleton sequence (g): R is Noetherian local, g is in its maximal ideal, g is a nonzerodivisor and R/(g) is regular local. The sequence definition also asks for a nonzero final quotient, which follows because (g) is contained in a proper maximal ideal. Thus the regularity-lifting node is applied with every hypothesis present, including at the generic point of E.

Step 8 uses lem-weil-pbc-regular-local-localization only after explicitly identifying the chart rings off E with A_x or A_y and their stalks with A_r. Its statement applies to every prime of A, with no excellence or smoothness assumption. The algebra isomorphisms and iterated fractions are written in the step. The regular-scheme definition then applies because local Noetherianity was already established. This avoids an unproved claim that the entire blowup is regular merely because its closed fibre is regular.

For step 9 I checked lem-weil-pbc-polynomial-ring-maximal-localization-dimension: it gives dimension n for every maximal ideal of a polynomial ring over an arbitrary field. Taking n=1 is legitimate for any closed point in either affine chart of E. The statement of lem-weil-pbc-dimension-quotient-nonzerodivisor requires a Noetherian local ring and a nonzerodivisor in its maximal ideal; all three conditions are supplied in step 6. The displayed equality therefore gives 2 without assuming the point is k-rational. Regular localness comes from step 7, rather than being silently inferred from the dimension equality.

I checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7 against the node and source statements. There are no new statement-only nodes to disguise an entire clause, no data definitions, no new Mathlib leaves, and no changed target or item statement. Every non-elementary step has existing-node citations and every citation has a verbatim quotation in citations.json. All nine steps are below 2000 characters. The small cases tested were A=k[[x,y]]; A=Z_p[[t]], where no coefficient-field argument is available; closed points defined by irreducible polynomials of degree greater than one over k; and the generic point of E. At that generic point the quotient local ring is a field and the ambient local dimension is one, so the dimension-two assertion must and does remain restricted to closed points. Dimension-zero and dimension-one local rings are excluded by the stated dimension-two hypothesis, not silently handled with two parameters.

The substantive correction during this review was to avoid applying the excellent global surface node to the arbitrary regular local ring. I retained its available smaller algebraic tools, replaced the off-divisor argument by explicit localization of the two charts, and proved the closed-point dimension clause separately. The only off-route result reported by the server is lem-trf-blowup-chart-regular-sequence-presentation (unit sk-i-curve-zero). It is a generic regular-sequence chart theorem, with no curve-specific hypothesis; its use here is a tool use in the source's affine blowup calculation, not a replacement of the six-functor/alteration route. I have not written a maintainer-owned tool_uses field.

Before this report, srvcheck.py review_split passed (0 new nodes; that generic tool use recorded) and srvcheck.py check_dag reported no finding introduced by the sandbox or on its nodes. The complete packaging dry run follows this signed review.

Final citation correction: after the first full dry run passed at f9d39a34c2d, I added the existing affine-spectrum quasi-compactness leaf to step 3 and its quotation to citations.json. This adds no node and changes no statement. The full dry run is repeated on this final version before push.
