# Q40 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fixed-residue-lifts-truncated-section.json: statement, split; no exact Mathlib match. Statement and statement dependencies retained unchanged.
- citations.json: seven verbatim full-statement quotes, one for each cited node in each proof step.
- report.md: this report. Searches are recorded by msearch.py in searches.jsonl.

No new nodes; no new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for fixed-residue and truncated-section notions. Algebra.artinian_lifting_truncated_section in AlgebraicGeometry/ArtinianLiftingTruncatedSection.lean:74 assumes lifting for every residue extension with inverse-image prime q. That hypothesis is stronger than this item's test with specified residue field k, so its declaration does not attach and its finite-kernel lifting theorem cannot be used as a black box here. Its docstring and the existing DAG proof are useful comparison material only.

## WANTED

None. All mathematical source material used is in literature/stacks-project/algebra.tex.

## Findings and corrections

There was no earlier sandbox split or report. The live item had no proof and is unsplit. No statement correction or STATEMENT-DISPUTED is needed. I retained its statement, citations and inherited searches, added only queries actually run through msearch.py, and supplied its proof.

The source is Tag 02HT, lemma-smooth-test-artinian, proof of (4) implies (1), specifically the paragraphs beginning “Let N” and “Applying condition (4)”. Its polynomial presentation is not needed for this subordinate lemma: C is already assumed Noetherian local and surjects onto A_q. The argument also works without exploiting that the displayed kernel is square zero. I followed the source's ideal filtration and truncation route, with explicit residue identifications instead of appealing to the stronger arbitrary-residue existing lemma.

Read SETUP's chapter/unit/node hierarchy, the assigned chapter and unit records, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md and sk-thm-sf-ctf-stability/_section.md. This is a generic algebra prerequisite of the inherited direct-image alteration route; it changes neither chapter nor unit. tools/blueprint_refs.py ancestor reports that the inherited ancestor is null. I retained that metadata rather than inventing an ancestor. Blueprint searches for “truncated section” and “fixed residue” returned no match. No unit realization record is applicable to this supporting lemma.

Mathlib searches were made through the required command: two different LeanFinder phrasings, LeanSearch, grep of RingTheory, and Loogle. Read all displayed hits and inspected Smooth/Basic.lean:126 (FormallySmooth.exists_lift) and LocalRing/ResidueField/Ideal.lean:204–226 (ResidueField.lift and liftₐ). The former assumes formal smoothness; the latter assumes q is killed, which the desired lift need not do. Neither supplies this implication. A first Loogle query contained an unknown identifier Ideal.Quotient; this diagnostic is recorded and was followed by a successful query for Algebra.FormallySmooth. No service error is counted as evidence of absence.

## Not duplicates

No new nodes were created. The related existing lem-weil-pbc-artinian-lifting-truncated-section uses arbitrary-residue lifting tests, and lem-weil-pbc-artinian-lifting-finite-kernel has the same stronger hypothesis. They cannot replace this fixed-residue statement. The existing Artinian ideal filtration, Noetherian local quotient, module-length definition and local unit criterion are reused directly.

## Review by Q40

I read the complete relevant portion of algebra.tex Tag 02HT against the item. Its successive small extensions have exactly the residue field required here: every quotient is formed from C by an ideal contained in m, and reduction is always the same map to C/m = S/qS = k. A map obtained by a lift automatically has the same residue composite, because the extension quotient induces the identity on these chosen residue identifications. No coefficient-field embedding into C or a test ring is being assumed.

Step 1 uses the statement of lem-weil-pbc-noetherian-local-quotient-artinian-local, which explicitly gives both Artinian locality and nilpotence of the maximal ideal. Its hypotheses hold because p inverse of qS is maximal in local C, hence is m, and both J squared plus m^N and J plus m^N lie in m and contain m^N. I checked the identification F = S/(qS)^N by image and inverse-image ideals, using surjectivity of p; it is not an unsupported assertion that an arbitrary local map preserves maximal-ideal powers. The localization definition node explicitly identifies the maximal ideal qS and residue field.

Step 2 uses the statement of lem-weil-pbc-artinian-ideal-length-one-filtration, which gives actual ideals in E with simple successive factors. Every filtration ideal is contained in ker(E to F), hence in the maximal ideal. I apply the same quotient theorem to their inverse images in C, checking both inclusions, so all intermediate rings are nonzero Artinian local with the prescribed residue field. The cited filtration node does not itself assert those intermediate-ring properties, and the proof does not pretend it does.

Step 3 uses only the explicit chain definition in def-weil-pbc-module-length: submodules for E and E/K_i coincide, because that scalar map is surjective. Thus the simple factors have length one over the source ring of each small extension, not just over E. The remaining argument is the finite downward induction applying the hypothesis of this item. I wrote its base, both commuting equations, the residue condition, and their preservation. No unproved general fixed-residue lifting theorem is hidden here.

Step 4 uses the full statement of lem-weil-pbc-local-ring-unit-criterion, read also against algebra.tex Tag 00E9, lemma-characterize-local-ring. Zero residue corresponds exactly to q, so every denominator outside q maps to a unit. The localization node gives the fraction equivalence relation. I wrote the fraction map, its independence of representatives by cancellation of a unit, R-compatibility, and equality after projection. This avoids importing a categorical-localization theorem that would not say the ring-theoretic assertion needed.

Step 5 is quotient descent written explicitly: b sends qS into the maximal ideal of E; its Nth power is zero by Step 1; hence it kills (qS)^N and descends. The section equation is checked on every element in the surjective image of S. It is not inferred merely from agreement on A, which need not surject onto F. No extra lemma is cited in this elementary quotient argument.

I checked delivery-errors B through E point by point: no new undefined notions, no new-node proof sketches, no unsupported tag citations, no use of a node's proof as its statement, no self-reference, and no replacement of the route. Every dependency actually cited has been opened and its complete statement quoted verbatim in citations.json. proof_deps is precisely the union of uses. All steps are below 2000 characters. Elementary steps are the same-submodule chain calculation and induction by the stated lifting hypothesis, and the final quotient descent; the algebra existence and unit steps cite their actual theorems. The generic algebra tools are declared in split_report.tool_uses.

Small cases checked: N=1 makes both ideals equal m and the section the identity; J=0 gives an empty kernel filtration; any other zero-kernel filtration has r=0 and the base alone suffices. A field C is allowed and makes all these maps identities. Surjectivity onto the nonzero localization excludes the zero ring C, and every intermediate ideal stays proper. No finiteness of k, characteristic restriction, finite type of A over R, or completeness of C has entered the proof. There is no use of SGA.

## Unfinished work

None in the mathematical split. The required server dry run and push are performed after this report is written; their outcome is the final delivery result.
