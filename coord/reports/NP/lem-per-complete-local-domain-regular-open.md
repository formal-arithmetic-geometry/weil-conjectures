## Worker report

Item: lem-per-complete-local-domain-regular-open. Group NP. Stage 1, direct delivery. Date: 2026-10-19.

### Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-complete-local-domain-regular-open.json: statement, split into ten proof steps; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for every cited node in every step.
- report.md: this report and review.

New nodes: 0. New Mathlib leaves: 0. The item uses existing Mathlib leaves, but does not create them.

### Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 and the read-only master source for the exact blueprint tag, complete local domains, regular opens, regular-locus names, and the relevant algebra names. No project declaration states this item. In particular an upstream sorry is not treated as an attachment. The item has no slopmaster2 declaration recorded in its node.

### WANTED

None. The source of the item and of all auxiliary algebra facts used here is available in the local Stacks checkout.

### Problems found and corrected

The imported node had no proof or proof dependencies. Its statement agrees exactly with Stacks 07PI after expanding J-0 using 07P7, so the statement and statement dependencies are unchanged. No statement dispute or target change is needed.

The source's reduction to intermediate finite ring models and its last passage from the monogenic hypersurface to the larger finite algebra were compressed. The split writes both out: B(M)=A intersect M is finite over the Cohen regular subring, has fraction field M by the explicit integral-equation inverse formula, and finite module generators of E over A_0 give a common denominator c with E_c=C_c for C=B[z]. The proof only claims the regularity on this further open; it does not silently identify the two orders before shrinking. This is a detail supplied to the source proof, not a claim that its theorem is false.

The finite field-extension induction is presented as a separable-first decomposition followed by a finite pth-root tower, using the already existing nodes for 030K and 09HI. This realizes the same separable / degree-p inseparable cases of 07PI and avoids an unstated induction hypothesis about arbitrary intermediate rings. No unit or chapter route changed. The existing nodes of other units are generic algebra tools, explicitly declared in split_report.tool_uses when not Mathlib leaves.

### Unfinished work

None for this one-level split. Existing auxiliary nodes are reused through their statements; this delivery does not modify or split them.

## Not duplicates

No new nodes were created. Searched the whole DAG by J-0, the four Stacks labels and tags 032D/07PB/07PH/07PG, regular subrings, derivations, finite fraction extensions, and purely inseparable towers. Read the existing nodes returned. Blueprint searches for J-0, regular subring, complete local domain regular open, inseparable and finite field extension found no blueprint node stating this item. The existing 032D, 07PB, 07PH and 07PG nodes, together with the existing separable-first and pth-root tower nodes, supply all non-elementary inputs, so no duplicate or restatement child was added. The item's blueprint.from place was already precise and is preserved; same_as remains empty. No unit realized fields are touched because the item is not the unit's key statement.

## Review by NP

I read More on Algebra 07PI (lemma-complete-Noetherian-domain-J-0) and 07P7 (definition-J), including the complete proof of 07PI. The hypotheses are exactly a nonzero Noetherian local domain complete for its maximal ideal; the output is a nonempty open on which the localizations are regular local. I also read the chapter and sk-p-dl-a1-perverse unit, the current blueprint ancestor's place and the original item's ancestry. This assertion is a supporting algebra input to the existing complete-local excellence route, not a replacement proof of the perverse-sheaf unit. No SGA source is used.

For the supporting inputs I opened every cited node statement, not merely its dependency list or proof. The relevant source places read were Algebra 032D (lemma-complete-local-Noetherian-domain-finite-over-regular), 00IK (lemma-Noetherian-basic), 00FN (lemma-Noetherian-permanence), 00GK (lemma-finite-is-integral), and the regular-local localization statement 0AFS; Fields 030K (lemma-separable-first) and 09HI (lemma-finite-purely-inseparable); More on Algebra 07PB (lemma-J-0-goes-up), 07PH (lemma-find-D), 07PE (lemma-derivation-extends) and 07PG (lemma-degree-p-extension-regular). The existing localization nodes explicitly state the general localizations used. There are no new nodes whose hypotheses or Mathlib verdict need separate review.

1. Step 1 uses lem-weil-pbc-complete-local-domain-finite-over-regular for the actual complete regular local subring and module finiteness, not just the existence of an unspecified regular ring. lem-weil-pbc-regular-local-localization says all its prime local rings are regular. lem-trf-finite-domain-fraction-degree applies to the injective inclusion of domains and supplies the finite fraction-field extension. Nonemptiness follows from the prime zero ideal in this subring, which is a domain because it sits inside A.

2. Step 2 uses lem-weil-pbc-noetherian-submodule-finite: A intersect M is an A_0-submodule of the finite module A. lem-weil-pbc-finite-algebra-noetherian gives its Noetherianity. A module generating family generates the algebra since its linear span is already the whole ring, so there is no unstated finite-type theorem here. Each B(M) is a domain since it is a subring of the field M.

3. Step 3 uses precisely the monic integral equation supplied by lem-weil-pbc-finite-algebra-is-integral. The written cancellation and inverse formula prove that inverting nonzero elements of A_0 already yields K; cancellation is valid because A is a domain. For x in M, the numerator sx lies in both A and M. This is the elementary fraction-field computation, not an uncited existence theorem for intermediate models.

4. Step 4 uses lem-weil-pbc-separable-first-purely-inseparable for the actual separable subfield M_0 and the purely inseparable quotient K/M_0. The statement covers characteristic zero by M_0=K. The input hypotheses to lem-exc-j0-separable-finite-type-ascent are checked individually: A_0 is Noetherian and a domain, its regular open is provided in step 1, its inclusion into B(M_0) is injective, finite type is step 2, and the separable fraction extension is step 3 and the decomposition theorem. That cited statement actually produces the required open in B(M_0).

5. Step 5 uses the tower clause of lem-weil-pbc-purely-inseparable-pth-root-tower, not merely the existence of a single inseparable element. Its finite purely inseparable hypothesis follows from step 4 and the finiteness in step 1. The induction assertion is the existence of a regular open in each specified B_i; the base and the final B_n=A are stated. No induction step is assumed in constructing the tower.

6. Step 6 is elementary from the existing tower data and step 3. Multiplying alpha_i by nonzero s from A_0 places z in E and places z^p in B; dividing a putative pth root by s proves the required non-pth-power condition. The degree-p relation gives injectivity of the monic quotient presentation: the remainder has degree less than p. This identifies C, not E, with the hypersurface.

7. Step 7 uses lem-weil-pbc-derivation-nonzero-on-non-pth-power with base A_0, which remains Noetherian complete local. B is a finite-type domain over that base even though B itself need not be local or complete; the cited statement allows exactly this. Its fraction field is M and the non-pth-power condition was checked in step 6. The principal open inside the induction open is a direct use of the Zariski basis, with h nonzero because the open is nonempty in a domain. The product hD(b) is nonzero in B.

8. Step 8 uses lem-weil-pbc-localization-noetherian for S=B_g; the local-ring identification is written as the maps on fractions. def-weil-regular-scheme then gives that S is regular. The localization clause (2) of lem-weil-pbc-derivation-extends gives a derivation on precisely this S with its unchanged value on b. D(b) is a unit since its product with h is inverted. These are all the hypotheses in lem-weil-pbc-degree-p-extension-regular, whose conclusion is the full regular ring S[T]/(T^p-b), with p at least one. The already proved monic presentation identifies that ring with C_g. No proof-internal construction of a cited node is used.

9. Step 9 writes the common-denominator argument explicitly. The generators are a finite A_0-module family of E, whose existence was already established in step 2. Their denominators lie in C because the fraction fields agree by step 6. Since A_0 is contained in C, their A_0-linear span E lies in C_c. The product c is nonzero in the domain C, and the two inclusions after localization give E_c=C_c. This is a short elementary argument from specified data, not a new lemma node.

10. Step 10 uses lem-weil-pbc-localization-of-regular-ring only on the already regular C_g, then the equality in step 9. lem-weil-pbc-principal-localization-open-immersion explicitly identifies Spec E_gc with the principal open D_E(gc). The product is nonzero in E, so zero is a point in that open. The local fraction maps from step 8 identify its local rings with E_q. This proves the induction step, and hence the item. No lying-over, normality, openness of the full regular locus, or excellence theorem has been assumed.

I checked the B--E failure modes against these exact statements: no new statement-only node is needed, no clause is moved into a renamed child, proof_deps is the union of uses, each quote in citations.json is the full verbatim statement actually opened, and every non-elementary algebra assertion is a cited node. Steps 3, 6 and 9 are the explicit elementary computations. No step exceeds 2000 characters; there is no long step hiding a comparison lemma. Existing off-unit tools are explained in split_report.tool_uses and are used as black boxes only.

Small cases checked: for a field the argument terminates in the separable case with nonempty whole spectrum; characteristic zero never enters the positive-characteristic derivation step; a trivial purely inseparable quotient ends at step 4, so no empty-tower indexing occurs; for k[[t^p]] contained in k[[t]], the tower has degree p and the scaling/hypersurface calculation has b=t^p in the lower fraction field but not its pth power, as required. The intermediate finite rings need not be complete or local, and no step assumes that they are. Products of denominators, h and D(b) stay nonzero because all rings in that portion are domains. Empty generator products use 1, so the denominator computation still has a defined value in that formal edge case. During review I replaced the finite-dimensional-endomorphism argument for the intermediate fraction-field equality by a cited integral equation followed by the explicit inverse formula, making its elementary content and assumptions transparent.

The new Mathlib audit for the item ran LeanFinder in two phrasings, Loogle, grep and LeanSearch through the prescribed msearch command. I read their actual hits: local DVR criteria, completeness of the completion, Krull dimension, smooth/unramified loci and topology do not assert the regular-open theorem. The successful searches are recorded as no match, not unavailable. Inherited searches and blueprint metadata were retained. No compiler, Lake, Lean-writing tool, shared-repository git command, or shared-file write was used.
