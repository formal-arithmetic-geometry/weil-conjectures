# Stage-1 delivery: lem-per-finite-etale-formal-monoid-coefficient-lift

Group Q117, 2026-10-19. Direct delivery, self-reviewed; independent maintainer review remains required.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-etale-formal-monoid-coefficient-lift.json: statement node, split into eleven steps, no exact Mathlib match. The mathematical statement and all original fields were retained; added proof, proof dependencies, proof origin, current searches and split report, and made the blueprint place precise.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The proof uses 22 existing dependencies, so it introduces neither duplicate nodes nor nodes restating clauses of the item. Steps 7 and 8 are explicit elementary finite-basis calculations, retained as steps rather than promoted to nodes.

## Attachments

None. Searched the slopmaster2 project source for the exact blueprint tag, formal-monoid/completion terminology, and henselian finite-etale lifts. HenselianFiniteEtale.lean contains the proper-scheme lifting declarations, with sorry in the main lifting theorem, and no declaration proving this formal-monoid statement. The archived master source is reference material only.

## WANTED

None. The actual source inputs are available in the local Stacks sources. ILO VI 2.3, printed p.73 (PDF p.79), was also read: it displays the equal- and mixed-characteristic completed Kummer charts, but does not state the present coefficient-lifting lemma for an arbitrary complete regular coefficient ring. Accordingly the new proof is marked agent-written, as an explicit consequence of cited Stacks results; it is not attributed verbatim to ILO.

## Audit of the original item and blueprint

The imported item was statement-only. It is true as written; no statement dispute or mathematical correction was needed. Its source advertises 031B for finite-module completeness, but 031B alone assumes separation. The proof now cites the existing Noetherian finite-module completeness node, whose 00MA formulation includes the required conclusion without an unproved separation assumption. The source also mentions regularity ascent 07NF: its hypothesis is a regular ring, not merely an unspecified regular local ring. Step 5 explicitly uses the existing regular-local localization theorem before applying ascent, and explicitly passes from affine etaleness to the ring-map definition of smoothness.

The current main-20261015 ancestor and the chapter/unit records were read. This item is the coefficient-extension detail in steps 5 and 8 of lem-per-completed-invertible-kummer-monoid-extension, below the ancestor's arbitrary-field duality ancestry. No perverse or chapter route was replaced. The Stacks algebra inputs from other units are generic tools, declared individually in split_report.tool_uses where applicable. The blueprint searches for 'finite etale', 'monoid completion', 'formal monoid' and 'coefficient lift', and whole-DAG keyword/tag searches, found no blueprint statement equal to this one. Relevant existing nodes, rather than new copies, are used.

Current Mathlib searches were run exclusively with msearch.py and read from the returned results: LeanSearch, Loogle, grep and two LeanFinder phrasings. They found general etale and separable-field infrastructure, polynomial coprime-factorization lifts, and finite-type descent, but no exact or one-line formal-monoid coefficient-lift theorem. The relevant Etale/Field, Henselian and Polynomial/UniversalFactorizationRing source signatures were inspected. The inherited search history is retained; current Q117 queries match searches.jsonl. No unavailable search is described as a negative result.

## Unfinished work

None in the one-level split. No Lean was written, compiled, or built. No live project or launcher file was changed.

## Not duplicates

No new nodes were created; therefore there are no new/existing pairs requiring a same-tag distinction.

## Review by Q117

I read delivery-errors B through E in full and reviewed the actual statements of every cited node. I also read the local Stacks theorem statements and their relevant proofs: 00FN/0316/05GG for completed monoid rings, 0325 and More on Algebra 0ALJ for complete local quotients and henselianity, 00GK and 00OI with 00GU for maximal-ideal contraction, 00U4 and 00U3 for etale fibres, 04GK and More on Algebra 09ZL for residue-algebra equivalence, 00MA for finite-module completeness, 0AFS/02GJ/00T2/07NF for regularity, 00U2 and 00NZ for flatness and a finite basis, and 00HR/05CK for the last clause. There are no new-node sources to review.

For each proof step I checked the following mathematical uses, not merely the existence of dependency ids:

1. **Finite-type permanence, completion Noetherianity, completion modulo its ideal.** The three cited nodes respectively say that a finitely generated algebra over a Noetherian ring is Noetherian, that its ideal-adic completion is Noetherian, and that a finitely generated ideal gives a complete completion with unchanged quotient modulo the ideal. Here E[S] is finite type because S has finitely many generators, and the ideal is finitely generated because E is Noetherian and S is fine. Sharpness makes the augmentation multiplicative, so its quotient is precisely k, not a different monoid algebra.
2. **Complete-local quotient and complete implies henselian.** The quotient theorem requires a proper ideal: f is in the maximal ideal, so (f) is proper, including f=0. The unique maximal ideal of H is proved by a convergent geometric series, rather than assumed from a completion theorem that does not say locality. Both E and A_0 are complete for their maximal ideals when the henselian criterion is used.
3. **Integrality, maximal-ideal contraction, etale maximal-ideal generation, finite separable residues, finite separable implies etale.** The first two cited statements ensure that the maximal ideal of the nonzero local finite algebra K lies over m_0. The next node says exactly that m_0 K_q is the maximal ideal; K_q=K. The residue theorem gives a finite separable extension, and the last node supplies its etaleness. No definition node is used as a theorem on fibres.
4. **Henselian equivalence, integrality/contraction, finite-type Noetherianity and finite-module completeness.** The equivalence supplies D and an actual k-algebra identification of its closed fibre with L. Locality is then proved: every maximal ideal lies over n and the quotient by nD is a field. This simultaneously proves m_D=nD; it is not inferred just from a residue-field identification at a single chosen point. Noetherianity and completeness have their own cited theorems, applied over the already complete Noetherian ring E. Nonzeroness follows from the nonzero closed fibre.
5. **Regular-local localization, affine etale comparison, the definition of smooth ring map, smooth regularity ascent.** The first statement upgrades E to a regular ring, exactly the hypothesis of ascent. The affine comparison gives finite presentation and vanishing H_1 and Omega. With Omega=0, its projectivity is elementary, so the cited definition really does give smoothness. The ascent result then gives regularity of D, and locality identifies D with its maximal-ideal localization.
6. **Etale implies flat and finite flat over a local ring implies free.** Both nodes have exactly the needed algebraic hypotheses, since D is finite over E. I wrote out why its basis is finite and nonempty; no freeness of an arbitrary infinite flat module is asserted.
7. **Definition of completion, with the fixed finite basis from step 6.** The equality m_D=nD identifies the two ideals of completion. The basis explicitly identifies their powers and every quotient; a compatible inverse-limit element is exactly a finite tuple of compatible coordinates. The resulting coefficient map respects multiplication at each finite quotient. Thus this is an elementary finite-coordinate calculation, not an invocation of an uncited theorem that arbitrary tensor products commute with inverse limits. Its 1,041 characters contain no hidden independent comparison lemma: every direction of the map is given by these coordinates.
8. **Elementary quotient calculation.** The scalar f acts coordinatewise in that same basis. The map and inverse on quotient modules are explicit and induced by the ring map, so the coefficientwise f is the correct relation. This is a routine consequence of step 7; it does not create a new lemma restating the item's isomorphism.
9. **Etale base change and full faithfulness of the henselian equivalence.** Etale base change applies to the maps E -> D and E -> A_0, without any regularity requirement on A_0. Finiteness is provided by the explicit basis. Both closed fibres have the specified k-algebra identification with L. The cited equivalence is the full equivalence, not merely existence of residue lifts: it supplies both morphisms, and faithfulness proves that they are inverses. This establishes an A_0-algebra isomorphism, rather than an abstract ring isomorphism.
10. **Completion modulo its finitely generated ideal.** This node supplies completeness and the residue quotient, not locality. Locality is again proved by the geometric series. The image of f is in the defining maximal ideal, and the quotient topology is its maximal-ideal topology. A ring isomorphism between local rings carries the maximal ideal and all powers to each other, which proves continuity in both directions; the algebra topology on K agrees because m_0K is its maximal ideal.
11. **Flat local implies faithfully flat and faithful-flat ideal contraction.** Step 6 provides flatness and step 4 provides locality and m_D=nD. The ideal-contraction node explicitly applies to every ideal, hence to n^2. Since (nD)^2=n^2D, contraction is exactly the claimed preservation of nonzero cotangent classes. It is not the stronger, unnecessary assertion that an arbitrary flat map preserves these classes.

I checked small cases before accepting the split: S={0}, E a field, f=0 (so the assertion becomes the residue-field lifting statement); S=N and f a square monomial (A_0 is nonreduced but still complete local and henselian); E=Z_p, S={0}, f=p (K is a separable residue field, whereas D is an unramified mixed-characteristic lift and p remains outside m_D^2); and n=0, where the cotangent assertion is empty. The zero monoid requires no nonzero generators, and none of the steps uses f as a nonzerodivisor. The excluded zero K cannot enter the argument; L is a field and D has positive basis rank.

I corrected draft source tags 00GH to 00GK and the maximal-contraction citation to 00OI with 00GU after checking the tag map against the actual labels. These were citation repairs, not statement changes. All proof steps are below 2,000 characters. Citations.json contains verbatim text from the current statement of each cited node, including all the hypotheses used above. No sources from SGA are used.
