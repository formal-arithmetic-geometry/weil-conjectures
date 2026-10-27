# Q48 stage-1 report: lem-pur-fixed-pair-right-adjoint-comparison

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-fixed-pair-right-adjoint-comparison.json — statement, split into five explicit steps; Mathlib does not state the entire fixed-pair comparison. Existing Mathlib leaves discharge generic transposition and adjoint uniqueness.
- citations.json — one verbatim statement extract for each of the five step/citation pairs.
- report.md — this report.

There are 0 new nodes and 0 new Mathlib leaves. searches.jsonl is the search command's existing output, retained without alteration. The original item's earlier searches were preserved and this session's actual logged searches appended to mathlib_searches.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, fixed-pair terminology, and rightAdjointUniq did not find a project declaration stating every clause of this item. IsoAlgebraAdjunction.lean supplies the existing construction of a lift, not the assertion determining an arbitrary prescribed lift's structure and comparing an arbitrary other right adjoint. No compilation was run and no attachment is claimed.

## WANTED

None. The categorical argument is written by the agent from the available adjunction reference and explicitly marked proof_origin.by = agent.

## What needed repair

The live item had an empty proof. Its hypotheses already correctly assume that the mate e is invertible and that the lifted adjunction counit has precisely the original counit as carrier. Both are retained; no statement correction or dispute is necessary. The split does not infer invertibility of a mate just from invertibility of beta, nor try to cancel F or epsilon as if they were faithful or monic.

The incoming blueprint.from.node is null. The required tools/blueprint_refs.py ancestor command also prints None, although the parent lem-pur-weil-smooth-dualizing-complex has a separate link to lem-a1-local-boundary-duality. I retained the imported null, existing via, and explicit place, and explained the actual blueprint use in split_report.blueprint. No chapter or unit record is changed: this is a categorical detail of a created helper, not the unit's key statement.

## Unfinished work

None at the requested one-level split. No new unsplit lemmas are needed. Delivery validation is recorded by the required dry-run output.

## Not duplicates

No new nodes. The generic right-adjoint comparison is already det-sp-unique-right-adjoint (a Mathlib leaf), and the inverse Hom-bijection formula is already lem-weil-pbc-adjunction-of-natural-bijection (a Mathlib leaf). Both are cited rather than recreated. The fixed-pair and mate definitions are also existing leaves. Whole-DAG searches by fixed-pair, adjunction, counit, hom-bijection and uniqueness terminology, plus blueprint_refs searches for fixed pair, adjoint, right adjoint uniqueness and counit, found no blueprint node stating the whole item. lem-sf-fixed-pair-adjunction-lift constructs the canonical lift; it does not determine the structure of a supplied carrier-normalized lift, so it is not an exact attachment or duplicate of the item.

## Review by Q48

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md's three-level rule, GOAL.md, the worker role, the chapter and unit records, and delivery-errors B–E in both its current and merged copies. The route is unchanged: the opening paragraph of the current main-20261015 lem-a1-local-boundary-duality proof uses smooth purity to identify the dualizing object; its parent helper needs the identification to hold for the assumed Weil right adjoint. I read the current cor-pur-adic-and-rational-smooth-dualizing-complexes proof and prop-weil-operations proof. They supply the intended purity/Weil context, not a hidden assertion of categorical uniqueness. The present split supplies that categorical argument explicitly. No SGA source is used.

For the actual categorical proof I read Stacks categories.tex, Tag 0037, definition-adjoint and the following paragraph's equivalent descriptions (1)–(3). Its inverse transpose is counit after F of the map. I also read all four paragraphs (Transposes, Naturality, Inverse, Uniqueness) of the current det-sp-unique-right-adjoint blueprint proof, and the project IsoAlgebraAdjunction.lean transport/counit formulas. There are no new nodes needing additional sources. Mathlib Basic.lean:160–171 and 182, Mates.lean:84 and 123–126, and Unique.lean:102–140 were read to check the returned generic hits and existing leaf interfaces. The algebra/coalgebra equivalence in Endofunctor/Algebra.lean concerns adjoint endofunctors on one category, not this comparison. Generic adjoint-lifting search hits need their own lifting hypotheses and do not specialize in one line to the whole item. The first interrupted LeanFinder search completed: its eight named hits were read from searches.jsonl rather than rerun; the required alternative wording was then searched separately.

Step 1 uses exactly the morphism equation in def-weil-endofunctor-fixed-pair-category. Substituting the source structure F(vartheta) beta and the prescribed carrier epsilon gives epsilon F(vartheta) beta = theta P(epsilon). Postcomposition on the source side with beta inverse gives the displayed equation. This is an elementary substitution and cancellation of an explicitly supplied isomorphism. No categorical comparison theorem is hidden here.

Step 2 uses the transpose characterization in def-weil-pbc-adjunction-mate and, concretely, the item's displayed mate hypothesis. Naturality of the original adjunction counit at theta: PK -> K is epsilon_K FG(theta) = theta epsilon_PK. Substitution of the displayed mate equation gives exactly the same FQGK -> K map as step 1. The subscript PK is necessary and was checked; all compositions are ordinary right-to-left as required by the statement. This is a three-line naturality/substitution calculation, so no separate node is warranted.

Step 3 cites lem-weil-pbc-adjunction-of-natural-bijection, whose statement explicitly gives Psi inverse(b) = epsilon_Y F(b). I read the full statement, not merely its title or proof. Apply the inverse Hom equivalence at X = QGK and Y = K to the two parallel maps QGK -> GK. Equal images imply equality by injectivity. Its hypotheses are precisely the original supplied F adjoint G. This proves the structure formula without assuming a lifted unit agrees on carriers, or requiring F to be faithful. The candidate structure is invertible because G preserves the explicit inverse of theta and e_K is supplied as an isomorphism.

Step 4 cites the full statement of det-sp-unique-right-adjoint. I checked that it asserts naturality, two-sided inverses, and uniqueness among all counit-compatible families, not just existence of some comparison. Its first right adjoint is the item's J, and its second is the item's tilde G, so the direction is J -> tilde G and the equation is tilde epsilon composed with tilde F(alpha) = kappa. Both adjunctions are assumed in the item. This existing Mathlib leaf is a generic tool and does not replace any unit-level geometric route.

Step 5 uses the forgetful functor in def-weil-endofunctor-fixed-pair-category, whose statement defines the carrier action and composition. Forgetting the preceding equality and substituting the assumed counit carrier gives precisely epsilon_K F(For(alpha)) = For(kappa). No carrier identification of J is made. The target fixed pair is then the one determined in step 3. This is elementary application of a functor to an equality.

I checked delivery-errors B–E against the written files: no new statement-only or Mathlib-leaf schema issue arises; the statement was preserved; proof_deps is exactly the union of uses; citations use statements rather than internal constructions; every non-elementary inference is a cited Hom-equivalence or uniqueness result. There are no circular dependencies or newly created clauses masquerading as a split. Each step is below 650 characters, so none reaches the 2000-character long-step threshold. No report-only fact is silently needed by the proof.

Edge cases: if P and Q are identities and beta and e are identities, the calculation forces vartheta = G(theta); it allows arbitrary theta and noninvertible unit/counit. More generally P and Q need not be equivalences anywhere in the argument. Empty fixed-pair categories cause no exception: the pointwise formula is vacuous and the assumed adjunctions still permit the generic uniqueness theorem. For identity adjunctions with a nonidentity exchange beta, the mate is beta inverse, so the formula vartheta = theta beta inverse has the correct direction. The formulas use no finite-dimensionality, additive, triangulated, small-index colimit, coefficient or geometric hypothesis. All four cited nodes are Mathlib leaves, so there is no off-route unsplit geometric theorem to declare as a tool use.
