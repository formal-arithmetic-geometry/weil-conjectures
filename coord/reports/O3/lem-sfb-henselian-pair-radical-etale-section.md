# Stage-1 delivery: lem-sfb-henselian-pair-radical-etale-section

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-henselian-pair-radical-etale-section.json: statement, split; no Mathlib match.
- citations.json: verbatim statement excerpts for all four step/node citations.
- report.md and searches.jsonl: report and search evidence.

No new nodes. No new Mathlib leaves. The existing nil-ideal idempotent-lifting Mathlib leaf is reused.

## Attachments

None. Searches of WeilConjectures by the exact blueprint tag and by henselian/radical/section terminology found no declaration of this item. HenselianOfEtaleSectionLifting proves the opposite implication; HenselianEtaleRetraction assumes a local ring; neither states the item. The existing Gabber-root section lifting theorem is a tool with extra polynomial hypotheses, verified in this split.

## WANTED

None.

## Audit findings and changes

The item was unsplit and the sandbox had no earlier node, proof or report. The statement is correct and unchanged. Its existing statement dependencies define exactly henselian pairs and etale morphisms. No target statement, unit, chapter, source file or repository file was edited.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None. I preserved it and the full inherited via chain rather than inventing an imported blueprint ancestor. Its explicit from.place already locates the supporting Tags 09XJ and 09XI in the affine-groupoid comparison below det-thm-sf-ctf-stability-direct-images, proof (3). I read the current latest blueprint unit and direct-images proof (3); the commutative-algebra input remains below that route. same_as is [] after blueprint searches for henselian, 09XJ, and etale section. No blueprint node states this assertion.

I avoided introducing a radical-invariance node or a general henselian-section-lifting node. The former is a short argument from an existing Mathlib leaf and the definition; the latter would replace the actual root-condition verification by a black box unnecessarily. Existing same-tag nodes were read by their statements: the Gabber-root lifting theorem and factorization criterion have precisely the two interfaces used. Quotient-henselian-pair is restricted to a local maximal-ideal pair, so it cannot prove radical invariance here.

Mathlib searches were executed with msearch.py and recorded literally as queries in the item. Earlier creator searches were preserved. The first grep used a directory path RingTheory/Henselian which does not exist as a directory; its empty output is explicitly marked inconclusive and was superseded by searches of Henselian.lean and RingTheory. I read Mathlib/RingTheory/Henselian.lean: HenselianRing is a root-lifting definition, not this section-lifting theorem; the semantic hits give square-zero/nilpotent lifting or lifting into complete rings, whose hypotheses do not apply. Two distinct semantic phrasings were read before deciding there is no match. No search was invented or recorded as unavailable when it succeeded.

## Tool uses

lem-weil-pbc-henselian-factorization-criterion is used as a generic commutative-algebra tool from another unit. Its complete equivalence supplies the Jacobson condition and monic factorization lifting for the radical pair. This does not replace the unit's geometric route; the current unit has no such algebraic criterion. It is declared in split_report.tool_uses. The other off-unit results are an existing Mathlib leaf and an existing closed theorem.

## Review by O3

I read Stacks more-algebra.tex Tag 09XJ, label lemma-change-ideal-henselian-pair, and Tag 09XI, label lemma-characterize-henselian-pair, including its (3) to (1), (1) to (5), and (5) to (2) arguments. I also read algebra.tex Tag 00J9, label lemma-lift-idempotents. There are no new nodes requiring separate source checks.

Step 1 isolates the zero ring so that the monic-degree argument later has a nonzero quotient. A unital algebra over the zero ring is itself zero; the requested map is unique. This is elementary and cites no node.

Step 2 uses exactly the nil-ideal bijection stated by lem-weil-pbc-lift-idempotents-locally-nilpotent and the finite-algebra idempotent definition stated by def-weil-pbc-henselian-terminology. I verified the nil hypothesis rather than assuming that a radical ideal is nilpotent: each element of JC/IC is a finite sum, and a separate exponent for each coefficient gives the displayed pigeonhole bound. No global exponent, finite generation, local-ring or Noetherian assumption is needed. Applying the leaf to C/IC and the kernel of its quotient by JC is legitimate, since the quotient is C/JC. Composition of the two bijections proves exactly the definition of (A,J).

Step 3 uses the full statement of lem-weil-pbc-henselian-factorization-criterion, not its proof or merely a definition. Step 2 supplies its henselian hypothesis for J. The displayed polynomial identity proves that the residue factors generate the unit ideal; both are monic and the original Gabber polynomial is monic. The criterion supplies lifts g,h and the Jacobson containment. Since A is nonzero and every maximal ideal contains J, A/J is nonzero. A monic polynomial retains its leading coefficient 1 after reduction, so h is linear; its constant term gives alpha congruent to 1. Evaluation gives the required root. This is the explicit argument in Tag 09XI, (1) to (5), not an unstated root-lifting lemma.

Step 4 uses precisely the conclusion and both hypotheses of lem-weil-pbc-gabber-root-criterion-etale-section-lifting. I read its statement and the upstream declaration Algebra.exists_etale_section_lift_of_gabber_roots in WeilConjectures/RingTheory/EtaleSectionLiftingOfGabberRoots.lean, lines 67 onward. The source definition of etale agrees with the item's scheme-etale hypothesis, and the cited node itself uses that same scheme formulation. Step 3 verifies every extra hypothesis at J. Its conclusion is equality of the reduction of the actual sigma with the prescribed bar-sigma, so no comparison or compatibility assertion is omitted.

For delivery-errors B I checked self-containment, unchanged notions and TeX, actual Stacks labels, searches, existing Lean candidates and inherited blueprint references. For C I checked all cited statements and wrote their exact substrings in citations.json; every non-elementary input has a node. For D I checked that the proof performs the radical-ideal argument and root-condition verification rather than moving the item into a new node. For E I checked the zero ring, I=0, I radical, and a nonradical ideal such as (t^2) in k[[t]]. The finite-sum nil argument also covers nil ideals with no common nilpotence exponent. I= A is possible for a henselian pair only in the zero ring by the existing criterion; step 1 covers it. All proof steps are below 2000 characters and hide no independent non-elementary comparison.

## Unfinished work

None in the authorized split. No Lean was written and no compiler, Lake or build tool was run. Required server checks and direct delivery are recorded by the delivery command.
