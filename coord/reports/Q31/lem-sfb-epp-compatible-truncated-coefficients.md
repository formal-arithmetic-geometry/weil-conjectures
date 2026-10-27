# Stage-1 report: lem-sfb-epp-compatible-truncated-coefficients

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-epp-compatible-truncated-coefficients.json — statement, now split; no exact Mathlib match. No new nodes and no Mathlib leaves created.
- citations.json — seven entries, one per step/node citation, containing verbatim statements.
- report.md — this report. searches.jsonl is maintained by the authorized search command.

## Attachments

None. Searched WeilConjectures for the blueprint tag and compatible coefficient/residue-section notions. CoefficientResidueSection.lean supplies only characteristic-zero residue sections; FirstOrderPowerSeriesComparison.lean requires a Noetherian complete local ring and gives only one coefficient section. NilpotentCoefficientAdjustment.lean has finite-generator and cotangent hypotheses and does not assert the required relative coefficient section. DifferentialCoordinatesCotangentIndependent.lean mentions sections in a docstring but its theorem is about cotangent independence. None proves every clause under this item's hypotheses.

## WANTED

None. All mathematical sources needed are present in literature/stacks-project/.

## Corrections and scope

The imported statement is correct and unchanged. Its empty proof has been replaced by the argument of Stacks more-algebra.tex, Tag 09EZ (lemma-cohen), with the formal-smoothness argument expanded into finite square-zero lifting inductions. No Noetherian or Artinian hypothesis is added: nilpotence of the maximal ideals does not imply either, and no such implication is used. No algebraicity or finite generation of l/k is assumed. Existing mathlib_searches are retained and actual logged searches appended. Read the second LeanFinder response before recording its lifting hits; they require formal smoothness and do not prove the whole item in one specialization.

The inherited blueprint.from.node is null, as confirmed by tools/blueprint_refs.py ancestor. Retained the recorded descriptive historical provenance and via chain. Read the current latest blueprint chapter and sk-thm-sf-ctf-stability unit and direct-images proof (3); it does not itself state this auxiliary Epp algebra fact. Nothing at unit or chapter level is changed. Whole-blueprint searches for 09EZ, coefficient-field, coefficient sections and residue section gave no equivalent item; unrelated coefficient sheaf statements are not duplicates. Tag search finds only this item and its Artin–Schreier parent, whose proof uses the item rather than supplying a smaller replacement. Existing generic lifting and separating-basis nodes are reused.

## Unfinished work

None in the stage-1 split. The cited square-zero lifting theorem is an existing reviewed split, not a claim of completed Lean. This delivery writes no Lean and runs no compiler, Lake or build tools.

## Not duplicates

No new node was created. In particular, no separate residue-section theorem or nilpotent lifting theorem is introduced: these would be routine steps from the existing square-zero lifting statement.

## Review by Q31

I read Tag 09EZ, lemma-cohen, in more-algebra.tex: its first sentence constructs the lower section by formal smoothness over F_p, and its second constructs the upper section relative to the chosen lower one. I also read algebra.tex Tag 0322 (proposition-characterize-separable-field-extensions), Definition 030O (definition-separable-field-extension), and Tag 030Z (lemma-perfect). These distinguish arbitrary separability from separable algebraicity; the upper residue field may be imperfect and arbitrarily large. There are no new-node sources to audit.

For step 1 I opened lem-weil-pbc-perfect-field-separating-basis and def-weil-pbc-separable-field-extension. The former assumes only a perfect lower field and finite generation of the particular intermediate field, and supplies its separating transcendence basis and separable algebraic residual extension. The latter defines arbitrary separability by exactly these finitely generated intermediate fields. Applying the former separately to each intermediate field proves the latter for k/F_p and l/k, without imposing finite generation on either whole extension. F_p is perfect because its Frobenius fixes the prime subring. The item's characteristic-p assumption passes to its nonzero residue fields.

For step 2 I read the complete statement of lem-sfb-separable-field-square-zero-lifting: it allows any commutative base-field algebra D, any square-zero ideal J, and an algebra map from the arbitrary separable extension into D/J. I use it with base F_p, extension k, and D=R/m_R^(n+1). The source and target structures come from the prime field. I wrote the induction base a_1=id, the induction range 1<=n<u, the identity D/J=R/m_R^n by representatives, and the square-zero calculation 2n>=n+1. Reduction of a_(n+1) is a_n, so induction retains the residue-section equation. Nilpotence at u finishes it. The cited def-weil-pbc-algebra-hom-quotient explicitly supplies algebra maps, ideal powers, quotient maps and quotient algebra structures, not an unproved formal-smoothness assertion.

For step 3 I checked the same definition's precise algebra-map equation. The displayed residue computation uses the definition of the induced residue-field map and the section equation already proved. This is an elementary calculation, marked so, and makes the identity on l a k-algebra map for the structure on S induced by f s_R.

For step 4 I reread the lifting statement with base k, extension l and D=S/m_S^(n+1). Its only field hypothesis is the general separability proved in step 1, not algebraicity. The quotient and square-zero checks are the explicit calculation of step 2 with S substituted for R. The base is b_1=id_l and induction stops at v. Every lift is a k-algebra map, so its defining equation is s_S bar(f)=f s_R; this proves compatibility, rather than merely asserting that chosen independent sections commute.

I checked delivery-errors B through E against these files. Unsplit new-node form and search/line requirements for new Mathlib leaves are inapplicable because there are no new nodes. Every cited statement was opened and its quoted text copied literally into citations.json. All non-elementary inputs are cited; the quotient identifications are proved by representatives within the steps. The proof does not move either clause into a new node, use another node's proof, or depend on the parent item, so it introduces no circularity. No step exceeds 2000 characters. The separating-basis and quotient-definition inputs are Mathlib leaves; the general square-zero lifting node is already in this same unit. No off-unit tool declaration is needed.

Small-case checks: u=1 or v=1 makes the corresponding induction empty and gives the identity residue section. For a field map R=k to S=l the construction gives the original map's algebra equation. For S=l[epsilon]/(epsilon^v), l need not be perfect; only the lower field k must be perfect, and l/k is covered by arbitrary separability. Arbitrarily large square-zero vector-space ideals are allowed, so the argument does not conceal finite generation of the maximal ideals. The excluded mixed-characteristic ring Z/p^2 is not characteristic p, avoiding the familiar impossible residue section there. The condition that rings be nonzero ensures that residue fields and their prime-field algebra structures exist.
