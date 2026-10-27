# Stage-1 report: lem-sfb-connected-action-orbit-section-ampleness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-connected-action-orbit-section-ampleness.json: statement, split into eleven proof steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-pointed-generic-integral-action-square-power.json: new statement-only node, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-self-product-component-rank.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for every step/node citation.

Two new nodes, zero Mathlib leaves. No unit realization fields changed: this auxiliary item is not the statement of its unit.

## Attachments

None. I searched the live project under lean/WeilConjectures for the blueprint tag and the action/orbit/ampleness concepts. No sorry-free declaration proves every clause of this item. Mathlib results are not project attachments.

## Literature wanted

WANTED: Ning Guo, Divisors on coherent schemes and homogeneous spaces, March 31, 2026 version, Proposition 6.4(b), for lem-sfb-connected-action-orbit-section-ampleness.

WANTED: the same document, Proposition 5.9 final assertion case (1) and Lemma 5.7, for lem-sfb-pointed-generic-integral-action-square-power.

WANTED: the same document, Lemma 4.3(i)-(ii), for lem-sfb-smooth-self-product-component-rank.

The local PDF named by the inherited source is absent. I read these places in the online primary PDF at https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf without downloading it into the repository. Lemma 4.3 is on printed p.10, Proposition 5.9 and Lemma 5.7 on printed pp.14-15, and Proposition 6.4 on printed p.16 in that version. The item's inherited printed-p.15 reference is retained as source history; the proposition number is the unambiguous locator. The detailed assembly proof is marked proof_origin.by=agent, since its local source is unavailable and its explicit induction/descent argument is mine. No SGA source is used.

## Problems and corrections

The imported statement is valid and unchanged. A square condition must not be added to it. The main repair is to make the preliminary pointed case, the strong induction, and the descent argument explicit rather than treating the square-power result for the acting group itself as a result about every action. The source's component-count argument needs an induction assertion over every normal integral affine Noetherian base, since its next bases are affine opens of Y. I stated that assertion. In particular, the diagonal component's count is one, not necessarily smaller than N, and it is handled by the pointed case instead of the induction hypothesis.

A second necessary clarification is that the image of Y in S may be a proper open U and need not be affine. The proof descends relative ampleness over U and then uses ampleness of O_U to obtain absolute ampleness. It never assumes Y -> S is surjective or U affine. Component invariance, affine section loci after base change, the family form of fpqc covering, and clopen assembly are written out. These are short deductions from the cited statements, not extra nodes.

I read the current chapter and unit, and the current blueprint under literature/blueprint/latest (main-20261024). Whole-blueprint and DAG searches found no equivalent statement for either new node. The inherited ancestry command returns a null nearest blueprint ancestor, so I preserve that null and the inherited via chain, add the item at the front for the new nodes, and give precise from.place explanations of the direct-image proof (3) auxiliary ampleness branch. I did not invent a new ancestor or change the unit route.

## Unfinished work

No missing argument remains in this one-level split. The two new genuine supporting theorems are intentionally statement-only and await their own stage-1 splits. Stage 2/3 and Lean implementation are outside this assignment. No Lean file, compiler, Lake command, repository file, launcher file, or git command was used to write this delivery.

## Not duplicates

lem-sfb-pointed-generic-integral-action-square-power vs lem-sfb-normal-group-square-power: the existing theorem concerns the acting group itself under translation; the new theorem concerns an arbitrary integral smooth H-scheme with a section and geometrically integral generic fibre. It is not a specialization of the translation theorem.

lem-sfb-pointed-generic-integral-action-square-power vs lem-sfb-dedekind-action-square-power: the existing theorem assumes a Dedekind (dimension at most one) base; the new theorem allows every normal Noetherian integral affine base, but uses a section and geometrically integral generic fibre. Neither extra conclusion is inferred by removing the existing dimension hypothesis.

lem-sfb-pointed-generic-integral-action-square-power vs lem-sfb-field-product-square-power: a product over a field is a different geometric input from the family/action square identity over arbitrary base changes; the new node is not the product statement restated.

lem-sfb-pointed-generic-integral-action-square-power vs lem-sfb-normal-product-square-descent: the existing product-difference descent input is not the positive-power square theorem for arbitrary pointed actions stated here.

lem-sfb-smooth-self-product-component-rank vs rem-pc-regular-normal: clause (2) of the existing remark gives integral clopen components, but no distinguished diagonal component, geometric generic rank one, or strict rank decrease for the other components.

lem-sfb-smooth-self-product-component-rank vs lem-sbc-smooth-section-component-geometrically-irreducible: the existing theorem describes the fibrewise component reached by a section; it does not give the finite global clopen decomposition of the self-product and the generic component-count identity needed here.

lem-sfb-smooth-self-product-component-rank vs lem-sfb-etale-generic-component-splitting: the existing statement allows shrinking and finite etale base change to split generic components; this node uses the actual self-product and diagonal, without shrinking S or replacing it by a finite etale cover.

The two new sources are Guo propositions/lemmas, not a reused Stacks tag. I searched the whole DAG by their literature place and concepts as well as the blueprint; no same-tag collision or equivalent stronger node was found.

## Review by Q15

I read Guo Proposition 6.4(b) for the item, including its preliminary pointed case and the reduction through the self-product. For the square-power node I read Proposition 5.9, especially the final assertion case (1), together with the square formulation in Lemma 5.7. The base is normal and integral; the generic fibre of H is geometrically integral because it is smooth and geometrically connected. The source's pointed case allows the special fibres of Y to have several components. The new node correctly chooses the exponent before all B,g,h, and allows the resulting error line N to live on B. It asks for no equivariance of the section and adds no commutativity or properness. For the component-rank node I read Lemma 4.3 with both factors Y and the graph of the identity. Smoothness provides the normal reduced generic fibres. The graph component has rank one; the remaining positive ranks sum with it to N, hence are strictly smaller. The affine-open clauses retain the same generic point and function field. They do not assert surjectivity to S.

I checked every cited node's actual statement, not its title. citations.json includes its verbatim text for each occurrence. In detail:

1. The affine qc/qs and local-Noetherian nodes apply to Spec A. The stalk-localization statement identifies exactly the rings whose normality is proved by denominator clearing. Smooth-normal ascent and finite-type-over-Noetherian give the required two properties of Y separately. Smooth-flat supplies local finite presentation; the finite-presentation definition supplies the qc/qs criterion. No regularity of S is used.
2. I use only clause (2) of rem-pc-regular-normal, which applies to a normal Noetherian scheme without assuming regularity. Connectedness of each residue-field group fibre, via the definition node, makes the finite clopen component label constant. The identity fixes the label, and inversion gives the inverse-image equality needed later. This also covers points defined only over field extensions.
3. The invertible-pullback-tensor node explicitly gives the residue-field section formula; a field extension preserves a nonzero coefficient. The affine-spectrum fibre-product node has affine base as required. A clopen component is also closed, so the closed-immersion node's affine preimage clause applies. The surjective-base-change node applies to the supplied orbit map. I use only original pulled-back sections; I do not claim all sections descend.
4. The new square-power node applies with exactly the section and geometrically integral generic fibre of this preliminary case. The existing square-action affine-orbit criterion has finite-presentation hypotheses, checked in Step 1, and requires exactly the square identity supplied by the new node. Passing from s to its tensor rth power preserves the locus. The ample-definition node then both recognizes ampleness of the power and proves ampleness of L itself.
5. The component node supplies every fact taken here: positivity/finiteness, the global decomposition, the diagonal section, rank one, and strict inequalities. The induction is strong and quantifies over all bases. The rank-one case does not circularly invoke itself.
6. The smooth-base-change clause of lem-pc-proper-base-change and the separated/finite-type-base-change node apply to H_Y. Geometric connectedness is stable directly from the field quantifier. The component node supplies nonempty integral restrictions to affine opens, their unchanged ranks and their sections. Step 3 verifies the restricted orbit-cover hypotheses. The acting group does not permute distinct components because Step 2 applies.
7. Every application of the pointed case or induction has an integral normal Noetherian total space and base, the inherited group/action/line, and the orbit cover. Only the i>0 components invoke induction. The ample-definition node applies after the explicit finite clopen gluing of sections by zero; there is no new comparison theorem hidden in this step.
8. Smooth-flat and flat-lfp-open give the open image. The smooth-restriction node applies to the factorization through U. The finite-affine-cover and affine-basis nodes provide the domains in the fpqc definition. I checked that its condition is on every affine target open, and supplied the finite subcover there using open images and quasi-compactness, rather than citing flatness alone.
9. I checked the relative-ampleness fpqc-descent node states descent for a supplied invertible module along a covering family and includes the scheme case. The factor swap and the equality of the products over U and S identify precisely that supplied line. Step 7 over every affine open verifies relative, not merely absolute-on-one-chart, ampleness on each B_j.
10. The quasi-affine basic-open criterion applies since U is a quasi-compact open of affine S. Its affine principal neighborhoods are exactly sections of O_U witnessing the ample definition. The relative-to-absolute twist node requires a quasi-compact map and an ample base line; both are checked. The isomorphism-invariance node transports the result along the tensor-unit identification, so no positive twisting line is silently discarded.
11. The normal-component node, smooth-restriction node, closed-immersion affine criterion, and ample definition are used with the same clauses as above. Separatedness restricts by the pullback of the diagonal; local finite type restricts to the open and quasi-compactness comes from Noetherianity. The orbit map restricts because components are invariant. The final section gluing proves the assertion for all of X rather than a single component.

I tested the edge cases: empty X is vacuous in the ample definition; nonempty integral Y has N>0; N=1 has only the pointed diagonal component; over a field with Y geometrically integral the self-product has only C0; a non-geometrically-integral smooth field extension gives multiple components with the diagonal one rank one; for an open immersion Y into S the image U can be proper and the descent still uses U. The trivial group reduces the criterion to the stated affine-section definition. For the pointed square node a trivial action works with r=1 and trivial N; a section need not be fixed by H. Disconnected special fibres and higher-dimensional normal bases are permitted by the cited case of Proposition 5.9, and are not replaced by a Dedekind assumption.

For Mathlib I read the recorded results of every required msearch invocation, including a second semantic phrasing per new node. The Picard-group hits CommRing.Pic.mk_tensor and mul_eq_tensor concern tensor products of modules over a ring, not action square powers. The geometric-irreducibility pullback hits require globally geometrically irreducible fibres or a geometrically irreducible morphism; they do not decompose a self-product whose generic fibre may be disconnected. The diagonal and component-set hits likewise do not imply the new statements in one line. All queries in the JSON are the actual logged queries. New nodes are therefore unsplit, not falsely marked Mathlib leaves.

I checked delivery-errors B through E against the finished files: there are no placeholder proof steps, new restatements of the item, source-only citations, circular induction calls, unintroduced objects, hidden square assumptions, or large unexamined steps. Every proof step is below 2000 characters. Elementary gluing, invariance and tensor-power arguments are written as steps instead of new nodes. The preliminary remote check_dag and review_split checks both passed; the final deliver.py dry run is the remaining admission check.
