# Stage-1 report: lem-sfb-fixed-hyperplane-restriction-cohomology

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fixed-hyperplane-restriction-cohomology.json`: statement, unchanged; split into six explicit proof steps. Mathlib verdict: no match after LeanFinder (two formulations), LeanSearch, Loogle and source grep using msearch.py. The inherited searches are retained separately from the newly executed Q40 searches.
- `citations.json`: 31 verbatim statement quotations, one for every node cited by every proof step.
- `report.md`: this report. No new nodes and no Mathlib leaves were created. The sandbox also contains the actual search log and the script used to write the JSON; neither is a new DAG node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id, hyperplane/Hyperplane, and cohomology/closed-immersion notions found no declaration stating this item. The invertible-module cokernel statements in Modules/HilbertPolynomial.lean cover only invertible modules, rather than arbitrary coherent E, and do not prove every clause here. The projection formula declarations also cover only one ingredient. They are not attachments.

## WANTED

None. All source material used is available locally.

## Issues found

No statement dispute. In particular the field need not be infinite: that hypothesis in Stacks 08A0 selects a section avoiding associated primes, whereas the item fixes a section and assumes the injectivity that the selection would provide. It would be invalid to apply the infinite-field existence theorem to identify the prescribed section. I instead proved its quotient directly using the existing general closed-immersion unit-quotient statement. The nearby regular-hyperplane and coherent-hyperplane-existence nodes were read and not cited: their existential statements do not supply a result about this particular section over an arbitrary field.

The inherited blueprint ancestry has `from.node: null`. Running `tools/blueprint_refs.py ancestor` confirms null. I preserved its detailed place and via list, and checked the current blueprint in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, specifically the direct-images proof (3). The item refines a prerequisite below that route and does not change the chapter or unit. The supplied unit JSON is older than the current blueprint section; no unit fields were changed, since this is not its key node.

## Unfinished work

None in this one-level split. Existing cited nodes retain their independent proof obligations. No Lean files were written or compiled.

## Not duplicates

No new nodes. DAG searches by 089Z, 08A0, 0EGK, closed-immersion quotient, tensor pullback, derived long exactness and projective twist cohomology found the existing tools used below. Blueprint searches for hyperplane, closed immersion, long exact, unit quotient and twist cohomology produced no alternate blueprint statement of the complete fixed-section item. The existing general tools were reused, rather than creating specializations.

## Review by Q40

I read Stacks varieties.tex Tag 089Z (lemma-hyperplane), all of Tag 08A0 (lemma-exact-sequence-induction), and Tag 0EGK (remark-exact-sequence-induction-cohomology). I also read modules.tex Tag 08KS (lemma-i-star-equivalence), coherent.tex Tags 089W (lemma-relative-affine-cohomology), 01XZ (lemma-coherent-Noetherian), the projective-space calculation in Tag 01XS including lemma-cohomology-projective-space-over-ring (01XT), derived.tex Tag 015B (lemma-higher-derived-functors), and cohomology.tex Section 01F7 (section-functoriality). I checked the current blueprint twist definitions, tensor multiplication and twist-cohomology statements as well as the current ancestor route. The proof is labelled agent-written because it adapts the sources to the fixed-section formulation and spells out additional compatibilities. There are no new-node sources to review.

For step 1 I opened and read the statements of def-pc-zero-scheme, lem-pc-twist-tensor, lem-weil-pbc-closed-immersion-unit-quotient and lem-weil-pbc-module-pullback-tensor. The first gives the ideal as the image of the dual section; the second gives exactly the local frame formula needed to identify multiplication's image with J E(d); the third explicitly states surjectivity and that kernel for every module, without flatness or quasi-coherence; and the fourth identifies the restriction of the tensor with the tensor of restrictions. The resulting quotient is the adjunction unit, so the restriction map is tracked, rather than an unspecified cokernel isomorphism. Injectivity is taken from the item's hypothesis, for this same integer d.

For step 2 I checked def-pc-proj, def-pc-projective-space-twist, lem-pc-zero-scheme-properties, lem-weil-pbc-finite-type-algebra-noetherian, pqf-def-locnoeth, pqf-lem-coherent-ft-locnoeth, def-pc-module-pullback and def-weil-closed-immersion. These statements supply respectively the affine degree-zero localization, its local frames, the zero-scheme affine quotient, Noetherianity of finite-type algebras, the affine-cover definition of locally Noetherian, the coherent/quasi-coherent equivalence under that hypothesis, pullback as scalar-extension tensor, and affineness of a closed immersion. The polynomial chart computation and the rank-one pullback-frame computation are written in the step. Every affine quotient is a finite-type algebra over the field, so the Noetherian theorem's hypothesis holds, including empty charts. Twisting G is locally an identity and hence preserves its already established quasi-coherence. This avoids silently treating the definition of coherent as the theorem that coherent modules are quasi-coherent.

For step 3 the statements of lem-sc-ringed-space-module-sheaves-enough-injectives and lem-sc-global-sections-left-exact verify exactly the source-category and functor hypotheses of lem-weil-pbc-derived-functor-long-exact. I read that last theorem's complete sequence, not just its title. pqf-def-cohomology identifies the functors with the module cohomology being used. This does not invoke the abelian-sheaf closed-pushforward cohomology theorem in place of module cohomology.

For step 4 I read the full statements of lem-weil-pbc-affine-morphism-cohomology-edge, lem-weil-pbc-module-cohomology-fmap-functorial, def-weil-pbc-module-cohomology-fmap and lem-weil-pbc-module-cohomology-fmap-basic-properties. The first explicitly identifies the edge map of the named definition and assumes quasi-coherence, already verified in step 2. The composition clause of the second gives edge composed with Hq(rho) equal to the cohomology map of rho. The definition calls the unit map pullback, and its degree-zero theorem identifies it with the actual section map. Thus there is no unjustified identification of two natural-looking maps. Boundaries after the edge identification are explicitly the old boundaries composed with the inverse edge; preservation of exactness then is elementary.

For step 5 I checked that lem-pc-projective-space-twist-cohomology supplies both the identification of H0(O(1)) with linear forms and H1(O)=0, including projective dimension one. Its other inputs are precisely the quotient, tensor and derived-long-exact nodes read in steps 1 and 3, plus the Proj and zero-scheme definitions. I wrote out why a nonzero linear form stays nonzero on every polynomial chart, why multiplication by it is injective there using leading coefficients, and why localization preserves that injectivity. Applying the already proved quotient calculation to O with d=1 gives the sequence whose H1(O) term vanishes. No infinite-field choice, projective-coordinate-change theorem, assertion that the prescribed section is the one selected by an existence theorem, or unproved hyperplane cohomology comparison is hidden in this argument.

For step 6 I reread the section-level clause of lem-weil-pbc-module-pullback-tensor and the precise local multiplication formula of lem-pc-twist-tensor. The step writes the coefficient calculation before and after restriction and checks it in the existing frames, so the asserted product equality follows from the cited statements in a few lines; it is marked elementary for that reason. The use of r_d is justified by step 4. It holds also for negative d, since all frame transition powers are invertible and the displayed tensor formula is stated for arbitrary integers.

I tested the small cases n=1 (in particular H is a point and H1(P1,O)=0), E=0, a sheaf supported away from H (G=0 and multiplication is invertible locally on its support), finite fields (no avoidance argument occurs), and arbitrary negative twists. The argument does not assert injectivity when E has torsion along H: that is explicitly excluded by the hypothesis. All steps have fewer than 2000 characters. I checked B--E of delivery-errors.md against the files: no statement was weakened, no new node repeats a clause, no circular proof tool is cited, no source tag substitutes for a non-elementary dependency, and every cited statement has a verbatim quotation in citations.json. A transitive statement/proof dependency search confirmed none of the cited tools reaches this item. Off-unit generic tools requiring declarations are recorded in split_report.tool_uses with the reason for their use.

The first delivery dry run rejected two quotation excerpts as shorter than its 40-character evidence minimum. I replaced both with the entire cited statements (finite-type algebra Noetherianity and enough injectives), including both hypotheses and conclusions, before rerunning. The standalone server review_split check passed.
