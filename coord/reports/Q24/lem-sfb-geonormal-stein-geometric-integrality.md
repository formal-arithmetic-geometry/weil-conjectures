# Stage-1 delivery: lem-sfb-geonormal-stein-geometric-integrality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-geonormal-stein-geometric-integrality.json: existing statement, split in five steps; no Mathlib match.
- citations.json: all twelve step/node citations, copied verbatim from their statements.
- report.md: this report. searches.jsonl is the search command's unedited log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, geometric-normal terminology, and Stein/separable constants. No project declaration states the item. Mathlib's integral normalization, finite_appTop_of_universallyClosed and geometric-integrality definition do not give this result. Read Geometrically/Integral.lean lines 35–120 and Morphisms/Proper.lean lines 150–169. All five fresh searches are logged, with both natural-language phrasings; the imported searches are retained as history.

## Wanted literature

None. Read the local Stacks sources.

## Corrections and observations

Statement unchanged; no statement dispute. The item has no proof or Lean audit in the current repository. Its source points to 0FD3, whose local varieties.tex label really is lemma-geometrically-normal-stein (some unrelated existing Bertini nodes use that tag differently). The source gives the connected-normal argument but does not itself explain the change from l to e; steps 2–4 write that calculation. In algebra.tex the base-change assertion of 00U2 is numbered (3), despite the existing base-change node's source saying (2); the existing node's mathematical statement is correct, and this delivery's step source uses the correct (3).

The ancestor command returns None. The inherited blueprint.from.node=null and via chain are retained; the from.place already specifies the exact extracted argument. Whole-blueprint searches for geometrically normal, normal integral, Stein, separable and geometric integrality yielded no equivalent statement. Read the current main-20261015 direct-images proof (3) and unit section, plus the DAG chapter/unit records. This lemma is a prerequisite within the existing alteration/constant-field route, not a replacement of that route. No unit realized fields belong to this non-key item.

## Not duplicates

No new node is proposed. Existing lem-pc-proper-geometrically-reduced-global-sections-separable supplies separability; lem-weil-pbc-finite-separable-extension-etale, lem-weil-pbc-etale-ring-base-change and lem-weil-pbc-etale-section-idempotent-splitting supply the multiplication factor; lem-weil-pbc-fibre-product-affine-spectra supplies the affine formula; lem-trf-geonormal-geoconnected-finite-type-integral supplies only the final criterion after geometric normality over e is proved; lem-weil-pbc-finite-type-over-noetherian supplies Noetherianity. Reusing these avoids creating clause nodes. The criterion alone is not an attachment or a duplicate of the present item: it assumes geometric normality over the intended base field and says nothing about the separable constants or multiplication component.

## Review by Q24

I read delivery-errors B–E in both copies, the worker brief, the three blueprint levels, GOAL, the stage document, and the relevant tool contract. I reread every cited node's statement, not merely its source or proof, and copied twelve verbatim quotes into citations.json. The following is the mathematical check of the five steps.

Step 1 uses def-pc-reduced-scheme's local-ring criterion and def-pc-geometrically-irreducible's all-field-extensions convention. A domain has no nonzero nilpotent, so the geometric-normal hypothesis gives exactly geometric reducedness. The quoted proper-global-sections lemma assumes properness, geometric reducedness, and that the structural global-sections map is a field extension. All three are present. It concludes separability, and finiteness is already an explicit item hypothesis. I read varieties.tex 0BUG, statement and proof of (4), and 038M. No assertion that a normal field extension is separable is used.

Step 2 uses precisely finite-separable-extension-etale, etale-ring-base-change, and etale-section-idempotent-splitting. The first applies to e/l after step 1; the second applies to l→e and l→E. The tensor-factor interchange is the explicit a⊗t↔t⊗a map. The splitting node requires an E-algebra retraction from the etale E-algebra R to E. Multiplication is E-linear and sends 1⊗t to t, so that hypothesis holds. Its statement supplies p, the kernel, and R≅E×(1-p)R; the spectrum of the first projection is the clopen D(p), which is a single component because Spec E is a point. I read algebra.tex 00U3 and 00U2 and more-algebra.tex 09XI's proof of (5)⇒(2), including its reference to 00U8. No Galois hypothesis or splitting field is needed.

Step 3 is an elementary affine computation using the full projection-aware statement of fibre-product-affine-spectra and the base-change definition. I checked both balanced tensor maps: multiplying the e-scalar b in A gives a well-defined inverse to a⊗t↦a⊗(1⊗t). The quotient by 1-p is an actual base-change ring, not an inference merely from a set-theoretic image. Its image is D(1⊗p), with complementary principal open defined by the complementary idempotent. The maps are structural tensor maps, so agree on any smaller affine chart and hence glue on overlaps. This proves the asserted canonical morphism, with its scheme structure, and pins the multiplication component. I read schemes.tex 01I4 and the existing affine-fibre-product statement. This is not a hidden general comparison lemma: it is the explicit two inverse maps for the objects constructed in step 2.

Step 4 is elementary: an open immersion preserves the ambient local rings, as the item's inline definition explicitly states. Thus each point of X×_e E has a normal domain stalk from X×_l E. The quantifier includes every E/e, proving geometric normality over e. The original finite affine l-cover is still the same cover of X as an e-scheme. Restriction of the structural global e-functions makes each chart an e-algebra, and its original l-generators generate over the larger scalar field as well. On tensoring, their images a_i⊗1 generate over E. This verifies finite type over e and over E without appealing to an uncited permanence theorem. I checked the definition node's finite-affine-cover criterion and varieties.tex 038M.

Step 5 uses the existing general geometrically-normal/geometrically-connected finite-type criterion, not its smooth specialization. Its statement assumes exactly nonempty finite-type X and the all-field-extensions normality and connectedness just verified. Nonemptiness and connectedness for E=e and for all E/e are explicit hypotheses. It gives geometric integrality, including nonemptiness, rather than merely irreducibility. The separate finite-type-over-noetherian node has precisely the Noetherian conclusion needed for each base change; Spec E is Noetherian directly from its two ideals, and step 4 has checked finite type. I read properties.tex 033M, its connected-normal explanation at 033O, varieties.tex 0FD3, and morphisms.tex 01T6. The finite-type hypothesis matters: connected normal schemes need not be integral in complete generality, as the local source explicitly warns.

I tested the construction on e=l (the complementary factor is zero and the canonical immersion is the identity), X=Spec e for a nontrivial finite separable e/l (multiplication selects one factor), and E/e transcendental (all proofs allow arbitrary E). The excluded inseparable Spec e example is not geometrically normal over l, and an empty scheme violates the explicit nonempty fibre hypothesis. No separably-closed, perfectness, smoothness, Galois, or finite-generation assumption on E is smuggled in.

B1–B10: no new nodes, no proof in a leaf, no invented searches, no attachment from an incomplete declaration; all notions retain existing statement dependencies and inline definitions, and TeX is decoded once. C1–C8: each non-elementary fact is a cited existing statement; only the explicit tensor, stalk, and affine-generator computations are elementary. Off-unit non-leaf tools are declared in split_report.tool_uses, with reasons. D1–D5: steps carry the component computation rather than moving the item into new clauses; there is no new node and no circular reliance on the item. E1–E7: hypotheses, schemes, retractions and structural maps are checked above. No source error changes the statement. All steps are shorter than 2000 characters. The existing parent uses this lemma; no parent is cited by this split, and the server checks the full DAG for cycles.

## Unfinished work

None at stage 1. Existing dependency nodes retain their own independent stage-1/Lean work. No repository or launcher file was written; no git command or compiler was run locally. Delivery is through the authorized delivery tool.
