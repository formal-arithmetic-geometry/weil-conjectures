1. Files written

- `dag/nodes/sec-six-functors/lem-sf-rational-thick-evaluation.json`: item, statement; split into twelve proof steps. Full completed sheaf-coefficient assertion is not a Mathlib leaf. All original Q94 searches are retained and the actual Q87 searches are appended.
- `dag/nodes/sec-six-functors/lem-sf-ringed-rhom-derived-complete.json`: new statement-only node, Stacks Tag 099A. Not in Mathlib: the searches return ordinary adic completion of modules, derived-category infrastructure, or condensed-module infrastructure, not ideal-adic derived completeness of internal Hom on arbitrary ringed sites.
- `citations.json`: one verbatim statement quotation for every step/node citation. Full statements retain the hypotheses for review.

2. Attachments

None. Search by the item tag and the notions in WeilConjectures found no project declaration giving all its clauses. The closest result `AlgebraicGeometry.Etale.derivedComplete_derivedHom`, IntegralCoefficients.lean:211, is for a constant coefficient ring on the small etale site, not arbitrary ring sheaves on slices. Its statement does not attach the item or the new general ringed-site lemma. Upstream master was used only as reference material, not proof evidence.

3. WANTED

None. All sources used are present locally.

4. Problems found and repaired

The item was statement-only. Its content is correct, and its statement and statement dependencies are unchanged. Its source place named a paragraph of `_section.md`; in the current snapshot the paragraph is in `sk-prop-sf-dualizable-biduality.proof.md`. I made that place precise and retained the original document pointer. The separate node proof `prop-sf-dualizable-hom.proof.md` is a termwise argument, while this item realizes the unit's exact-functor/direct-summand paragraph. I did not replace that route.

I checked the generic ringed-site statements rather than citing the etale constant-ring `lem-sf-hom-triangulated`, or the constructible-only tensor-completion result. Neither has the hypotheses needed for arbitrary slice objects here. The existing `lem-coef-integral-hom-reduction` states completeness on the global pro-etale site, but does not cover arbitrary ringed slice sites. That is why the smaller general 099A tool is needed. The tensor is always completed: the proof never identifies ordinary tensor with completed tensor for arbitrary objects. Nor does it require rational retracts to be integrally constructible or integrally split.

During self-review I corrected the triangle-isomorphism source to Tag 014A and replaced two over-specific or insufficient citations: scalar restriction on a slice is derived directly from its general definition (underlying abelian sheaf unchanged), and the chain-map representative into a K-injective uses the actual bijection in `lem-weil-pbc-kinjective-hom-derived`, not just the global-section formula for internal Hom.

5. Unfinished work

The new general 099A statement is deliberately unsplit, as required for a one-level split. Its source proof uses the tensor-Hom adjunction, slice restriction, and the vanishing of Hom from objects over a localized coefficient sheaf. The present item is fully split; it does not inline that non-elementary completeness theorem.

## Not duplicates

`lem-sf-ringed-rhom-derived-complete` vs `lem-coef-integral-hom-reduction`: the existing node concerns the completed coefficient sheaf on a scheme's global small pro-etale site and also asserts finite-reduction compatibility; the new node is the local-ideal completeness assertion on every small ringed site, for arbitrary ideal sheaves, including the slices required here. The existing node has no slice or arbitrary-ringed-site clause.

`lem-sf-ringed-rhom-derived-complete` vs `lem-weil-pbc-ringed-koszul-completion-reflector`: the reflector node constructs completion and characterizes its universal property for finitely generated global ideals; it does not say that internal Hom into a complete object is complete.

`lem-sf-ringed-rhom-derived-complete` vs `lem-weil-pbc-ringed-internal-hom-exact-restriction`: the existing node supplies the exponential law, restriction and exactness of internal Hom; it has no completeness conclusion.

`lem-sf-ringed-rhom-derived-complete` vs `lem-sf-rational-thick-evaluation`: the new node is an independent ringed-site completeness lemma, with no rationalization, evaluation map, tensor comparison, or thick-class conclusion. The substantive argument of the item stays in its twelve steps.

Whole-DAG searches by 099A/derived-complete-internal-hom, concept searches, and blueprint_refs searches for 099A, complete internal, derived complete, thick, internal Hom and evaluation found no blueprint node asserting this general lemma. The Lean declaration above covers a different site and coefficient encoding. The Mathlib searches were run using msearch.py and their real results read: IsAdicComplete and AdicCompletion in RingTheory/AdicCompletion/Basic.lean:56,171 concern ordinary modules. I also read the relevant definitions there. The second semantic wording likewise returned ordinary completion, not a match. No new Mathlib leaf is claimed.

`lem-sf-ringed-rhom-derived-complete` vs `def-weil-pbc-locally-derived-ringed-ideal-complete`: the existing definition specifies the local vanishing condition but makes no assertion that internal Hom into a complete object satisfies it; the new node asserts precisely that preservation theorem.

`lem-sf-ringed-rhom-derived-complete` vs `def-weil-pbc-ringed-site-ideal`: the existing definition constructs ideal subsheaves and extension of ideals and gives local criteria for a quotient-ring isomorphism; it has no derived internal Hom or completeness preservation assertion.

`lem-sf-ringed-rhom-derived-complete` vs `lem-weil-pbc-flat-ringed-ideal-complete-equivalence`: the existing theorem compares complete subcategories under a flat coefficient homomorphism and a locally finitely generated ideal; the new node proves closure under internal Hom for one arbitrary ring sheaf and ideal, without a coefficient homomorphism or flatness assumption.

`lem-sf-ringed-rhom-derived-complete` vs `lem-weil-integral-constructible-triangulated`: the existing theorem gives triangulated closure of bounded constructible complete complexes on a scheme's pro-etale site; it does not assert completeness of internal Hom for arbitrary unbounded complexes on arbitrary ringed sites.

## Review by Q87

I read the chapter and unit records, the main-20261015 unit statement and its separate proof, and both versions of the prop-sf-dualizable-hom node text. The twelve steps expand the unit sentence about exact functors and direct summands before the parent's bounded-complex induction. In particular this is not an application of the parent's evaluation theorem, which would be circular. The import's ambient scalar localization is retained throughout.

For the new node I read algebraization.tex, lemma-derived-complete-internal-hom (Tag 099A), including its proof and the preceding local completeness definition (0999). It assumes only a ringed site, an ideal sheaf, an arbitrary first object and a complete second object. I reproduced exactly that scope, with localization and slice restriction defined and cited. There is no hidden Noetherian or finite-generation assumption. Small cases: K=0, N=0, zero ideal, unit ideal (then N=0), an arbitrary unbounded K, and an empty site are consistent with the assertion. Its proof is a genuine independent lemma; it is not one of the closure assertions renamed as a new node.

Steps 1–2: I read proetale.tex Tag 099M (quotient-tower completion), algebraization.tex Tag 0A0E (Koszul completion and its unit), and the full statements of the coefficient-completion equivalence and reflector nodes. The Noetherian hypothesis belongs to O_E, which the existing DVR theorem supplies; it does not belong to X or to a slice. Both generic site theorems allow the slice as their original small site. The slice coefficient sheaf is the inverse limit of the restricted constant finite sheaves, because restriction is sectionwise. I read the K-flat change-of-rings and tensor-descent statements: they give exactly the representatives and naturality used in step 2. The displayed balanced tensor isomorphism checks each finite quotient and its transition. Completion of the ordinary tensor is not assumed to equal the ordinary tensor.

Step 3: I read the tensor cone isomorphism, K-flat cone closure, and the exact strict-tower derived-limit statement. Tensor exactness follows on cone representatives; quotient transitions are strict and preserve the cone maps, so exact derived inverse limit applies. It works without exact products on an arbitrary slice: the cited strict-tower theorem expressly imposes no exact-product hypothesis. Restriction of coefficients preserves kernels/cokernels because it changes the action, not the underlying abelian sheaf. This avoids using a global-pro-etale-only scalar-restriction lemma on a slice. Naturality of the completion unit uses the actual finite quotient maps and the strict tower, not an arbitrary choice of a lift into a Roos fiber.

Step 4: I opened the general ringed internal-Hom exactness/restriction statement: it permits arbitrary unbounded objects and arbitrary small ringed sites, so its hypotheses hold here. Together with step 3 it gives exactness of both functors; the componentwise scalar action gives O_E-linearity, including on shifts. Tag 099A applies to M after the precise completeness comparison in step 1, so it supplies exactly the complete target needed in step 5. I did not infer completeness from the definition of completed tensor or from constructibility.

Step 5: I read the canonical ordinary duality-map statement and sites-cohomology.tex Tags 08JD, 08JE and 0A98. They give the ordinary evaluation transformation for arbitrary objects, not its invertibility. The reflector bijection, whose target is now complete, constructs the completed comparison uniquely and proves its naturality by precomposition with the actual completion unit. Thus the statement's comparison is genuinely the evaluation map.

Step 6: I checked the Hom differential and tensor differential in their definition nodes and read the K-injective existence and Hom-to-derived-Hom bijection. The latter is what permits the chain map u used in the representative calculation. With the source written M tensor dual, no extra evaluation sign occurs. The first-variable shift sends a degree-a Hom to (-1)^a times it; moving that [-1] through a degree-b first tensor factor contributes (-1)^b. Their product is exactly the target degree-(a+b) sign. This proves shift compatibility for arbitrary L; it does not test only on a generating class. The symmetric source order is obtained by the same Koszul symmetry in both paths. I verified the negative shift by inversion and all integer shifts by iteration.

Step 7: I checked that the reflector statement gives injectivity of precomposition into any complete object. The target shift is complete because the localization-Hom vanishing criterion commutes with shifts, by the exactness statement already cited. Thus the two extended maps agree. Step 8 uses the exact statement of the scalar-localization triangle theorem: every distinguished triangle is isomorphic to the image of an integral one. The fraction formula defines the descended functors even on arrows that do not lift integrally; O_E-linearity makes it well defined. Naturality and the shift square persist after the same localization.

Steps 9–11: I checked coefficient-unit evaluation on an actual degree-zero free module, where evaluation at 1 and multiplication are inverse chain maps; the completion map is invertible because M is complete. Zero, binary sums and shifts then follow from the actual transformation. For retracts, I multiplied the displayed inverse on both sides and checked the order of i and p for contravariant functors. Both composites are identities; no lift of rational i,p or integral idempotent splitting is used. These steps are elementary calculations, not extra nodes.

Step 12: I opened lem-sf-triangle-morphism-iso and checked its last-square hypothesis. Naturality handles the first two squares and the explicit shift check handles the connecting square. The same contravariant triangle sign appears on both image triangles. Tag 014A therefore applies to the two isomorphisms, including any of the three choices of the remaining vertex. No equality-of-natural-transformations principle on thick generators is used.

For the whole item I tested M=0, L=0, L=R, positive and negative shifts, finite free sums, retract maps with denominators, the zero/empty-scheme case, and triangles with one zero vertex. The unit clause genuinely uses completeness: on a point an incomplete module would make the completion unit noninvertible, so that hypothesis was not dropped. Every proof step is shorter than 2000 characters. The non-elementary ingredients are cited nodes; the balanced tensor, sign, fraction and retract calculations are written out. All off-unit statement tools are declared in split_report.tool_uses with their particular role; they supply generic constructions, and no unit step is replaced. No SGA source is cited or used. I preserved all maintainer-owned fields and wrote only in this item's sandbox. Required server checks and delivery are recorded below as they finish.

Continuation review: the first required dry run identified four additional same-0999 comparisons. I opened each current statement and added the four explicit comparisons above. These nodes respectively define completeness, define ideals, compare complete coefficient categories under a flat map, and prove triangulated closure with constructibility. None states internal-Hom preservation of completeness, so the new Tag 099A node is retained.
