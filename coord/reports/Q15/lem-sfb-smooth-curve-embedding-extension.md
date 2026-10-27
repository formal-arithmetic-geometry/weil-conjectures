# Q15 stage-1 report: lem-sfb-smooth-curve-embedding-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-curve-embedding-extension.json: statement, split into four steps; no exact Mathlib match.
- citations.json: seven entries, with verbatim statements for every citation of every step.
- searches.jsonl: five new executed queries, including two semantic phrasings, Loogle, LeanSearch and Mathlib grep. Existing Q13 search records in the item were retained.
- report.md: this report.

No new nodes and no new Mathlib leaves.

## Attachments

None for the item. The project theorem AlgebraicGeometry.Scheme.exists_hom_of_valuationRing_stalk belongs to the existing lem-sfb-valuation-stalk-proper-target-extension. I read WeilConjectures/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean:40-91; it is sorry-free and the existing node's audit is closed. It takes an integral source with valuation stalks and an already specified generic-point morphism, rather than stating this item's smooth-curve and field-embedding conclusion. The projective-line theorem in Curve/SerreDuality.lean:234 is also too specialized in its target and assumes a proper source. Thus neither is an exact attachment for this item.

## WANTED

None. All sources used are present locally.

## Findings and changes

The original item was statement-only. Its statement and statement dependencies were retained, as were the source, provenance, blueprint from-node (null), inherited via list and all historical searches. There is no mathematical statement dispute. A null nearest blueprint ancestor is what tools/blueprint_refs.py ancestor prints for this chain; I have not changed maintainer-owned provenance to invent an ancestor. The latest direct-image blueprint proof has det-thm-sf-ctf-stability-direct-images as its frontmatter id; its present paragraph (3) does not itself contain the old auxiliary genus argument, so the inherited from.place is historical route information. This delivery proves the extracted mathematical lemma without changing any unit or chapter route.

The proof is an assembly of existing results, with all valuation and fraction calculations written out. I corrected the auxiliary DVR-extension tag in my source annotation to 0BXY after checking tags/tags. The source for the global extension remains Morphisms 0BX7, not a claim that 0BY1 requires Y to be a smooth curve. All step texts are shorter than 1000 characters.

## Not duplicates

No nodes were created. Searches of the whole DAG and blueprint found the general valuation-stalk extension node and the smooth connected curve local-ring node, which are reused. Searches included blueprint_refs.py search for function field, smooth connected curve, proper target, embedding and valuation ring, and DAG searches for 0BX7 and the local-ring concepts. The field-embedding extension is not the unrelated coefficient embedding-extension node. Mathlib's RationalMap.ofFunctionField and fromFunctionField_ofFunctionField (Birational/RationalMap.lean:516,520) produce a rational map and identify its generic restriction; they do not assert extension to the whole curve. The second semantic search found valuative-criterion existence statements, again insufficient for global extension as one-line specializations. I read those returned rational-map declarations and the existing project global extension theorem.

## Review by Q15

I read Stacks curves.tex:158-206 (0BY1), curves.tex:60-95 (0BXY and the normal-curve extension), morphisms.tex:10425-10472 (0BX7), morphisms.tex:12705-12713 (01RV), and schemes.tex:692-710 (01HV). I also read the normal-Noetherian and codimension-local-ring statements in properties.tex that support the existing curve local-ring node. There are no new nodes whose source needs an additional review. No SGA source is used.

For step 1 I opened the complete statement of lem-sc-smooth-connected-curve-local-rings. The hypotheses match exactly: algebraically closed k, smooth, nonempty connected, separated finite-type curve of dimension one. Clause 1 gives integrality and the generic field; clause 2 accounts for every nongeneric point; clause 3 gives its fraction field and the unit-times-uniformizer-power description. The sign of the integer exponent proves the valuation-ring alternative explicitly; no uncited DVR-to-valuation lemma is hidden. This existing off-unit node is declared in split_report.tool_uses solely as a local geometry tool.

For step 2 I opened def-weil-affine-spectrum and lem-sc-integral-function-field-affine-fraction. The former explicitly gives contravariance, functoriality and the description of Spec of a field; the latter applies to any integral scheme, so it applies to Y without smoothness or dimension assumptions and gives the injection and fraction-field identification. The generic morphism into an affine neighbourhood is Spec of its germ map by its definition. The displayed composition then gives the map on A. The k-linearity check uses exactly that the original embedding fixes k. This step is elementary relative to these statements. The affine-fraction node is declared as a generic tool of another unit.

For step 3 I opened lem-sfb-valuation-stalk-proper-target-extension, including its full statement and Lean source. It provides exactly F composed with i_C equals the chosen h, rather than mere existence of some morphism or an unspecified rational map. Step 1 supplies all source hypotheses; the item's properness hypothesis supplies the target hypothesis; step 2 supplies an actual k-morphism. At the Lean level Y.IsSeparated follows from properness over Spec k, and Spec k is separated. No properness of C, and no smoothness or dimension hypothesis on Y, enters the application.

For step 4 I again checked the Spec-of-a-field statement and the affine-fraction statement. Evaluating the extension identity on the unique points proves the generic image. Taking generic stalk maps uses identity maps for the canonical generic-point morphisms. Finally a ring homomorphism sends an inverse to the inverse of the image, so the fraction formula is exactly phi(a)/phi(b), with nonzero denominator by injectivity. This is a calculation from definitions and the two cited statements, not an additional geometric lemma. Every quote in citations.json was tested as an exact substring of the corresponding current node statement.

I tested the small cases: C affine line and Y projective line with t sent to 1/t extends across t=0, showing that source properness is unnecessary; the analogous target affine line would fail, confirming why target properness is used. Y=Spec k gives its structure map and all the stated generic identities. In positive characteristic the embedding t sent to t^p remains allowed and the computation still gives that map, so no separability was slipped in. At the generic source point the stalk is a field, not a DVR; this case is handled separately in step 1. The exponent-zero case and both exponent signs in a closed DVR stalk are covered. No claim about an empty or zero-dimensional source is made, since the item assumes dimension one and a nonempty connected curve.

Against B-E: no statement-only new nodes or duplicate clauses were introduced; every non-elementary fact is a cited node; all cited statements were opened; all hypotheses above were checked; Spec reverses arrows correctly; all TeX is single-escaped after JSON parsing; proof_deps is the union of uses; both off-unit tools are declared; no cited node depends back on this item; and no step exceeds the 2000-character review threshold. Nothing remains unfinished in the split.
