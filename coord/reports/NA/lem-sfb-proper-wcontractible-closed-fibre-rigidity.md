# Worker report: lem-sfb-proper-wcontractible-closed-fibre-rigidity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-wcontractible-closed-fibre-rigidity.json: item, statement unchanged, eight proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-wcontractible-jacobson-henselian.json: new statement-only ring lemma; Mathlib searches found no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-closed-torsion-rigidity-serre-transfer.json: new statement-only relative coefficient-transfer obligation; Mathlib searches found no match.
- citations.json: one verbatim statement quotation for every proof-step citation.
- searches.jsonl: the actual msearch service log; no entries synthesized.

## Attachments

None. Searched the exact blueprint tag and weak-contractibility/closed-fibre/henselian rigidity notions in lean/WeilConjectures, including the existing WeaklyContractibleCohomology, StrictlyHenselianStalk and ProEtale coefficient directories. No project declaration states this full coefficient and weak-Serre-hull comparison without sorry. Ordinary henselian/cohomology declarations and the finite-coefficient comparison do not cover the item.

## WANTED

WANTED: an exact source for closed torsion-cohomology rigidity implying rigidity on the ordinary weak Serre coproduct hull of finite scalar-model constructible modules, with all-continuous norm-topological algebraic-closure coefficients; for lem-sfb-closed-torsion-rigidity-serre-transfer. This is a new unsplit obligation, not a theorem claimed to be proved by HRS or RTW. The source place records its agent origin honestly.

## What was wrong or missing

The item had no proof and its source explicitly requested the general proper comparison. Its statement was retained byte-for-byte. RTW Proposition 1.1.2 proves the henselian closed-point geometry and Corollary 1.1.5 concerns sections on W itself, not arbitrary proper schemes over W. Neither was cited for the full comparison. The norm topology on Omega was retained: it was not replaced by the finite-subextension-valued condensed ring. HRS finite-type/Noetherian/finite-subextension statements would not supply that replacement.

The existing lem-sfb-qcqs-proper-constructible-closed-base-change cannot be used: its dependency path passes through lem-sfb-qcqs-proper-localizing-coproducts, lem-sfb-qcqs-proper-hull-tail-bound, lem-sfb-qcqs-proper-serre-heart-bound and this item. No such circular citation occurs in the delivery. The item remains in its given chapter and unit; no unit/chapter record was changed.

I did not assert that the class of modules whose restriction comparison is invertible is automatically closed under kernels and cokernels. Long exact sequences alone do not prove that. The entire nontrivial transfer to that closure is explicitly the new generic coefficient obligation. The proof of this item carries the classical torsion comparison and all geometry used to establish its hypothesis.

## What remains

Both new nodes join the stage-1 queue as unsplit statements. In particular the coefficient-transfer theorem requires a substantive later proof and an exact reference. This delivery does not claim that the full target or the coefficient transfer is already proved in Lean or that its source has been found. No Lean was written, compiled or built.

## Not duplicates

lem-sfb-wcontractible-jacobson-henselian vs lem-zl-condensed-henselian-lisse-rigidity: the existing node assumes a henselian pair and compares components and dualizable objects; the new node proves that the Jacobson pair is henselian from w-contractibility.
lem-sfb-wcontractible-jacobson-henselian vs lem-zl-henselian-wstrict-local-invariance: the existing equivalence assumes henselianity of a specified pair, whereas the new ring statement supplies that hypothesis.
lem-sfb-wcontractible-jacobson-henselian vs lem-zl-henselian-indetale-closed-lift: that statement concerns the designated closed-site lift of an already henselian pair, not Jacobson henselianity of a w-contractible ring.
lem-sfb-closed-torsion-rigidity-serre-transfer vs lem-sfb-torsion-cd-topological-serre-transfer: the existing node transfers an affine étale torsion vanishing bound to a higher-degree absolute cohomology bound; the new statement transfers a closed-pair restriction comparison in every degree and has no affine cd hypothesis.
lem-sfb-closed-torsion-rigidity-serre-transfer vs lem-sfb-proper-wcontractible-closed-fibre-rigidity: the new lemma has no proper morphism, weakly contractible base or closed-point construction; it assumes torsion étale cohomology rigidity of a general qcqs closed pair, which Steps 1–5 establish in the proper geometric situation. This is a relative coefficient tool, not a renaming of a clause under the item's hypotheses.
lem-sfb-closed-torsion-rigidity-serre-transfer vs lem-sfb-qcqs-proper-constructible-closed-base-change: that node is a sheaf-valued proper exchange for finite-Tor generators with a qc complement and a proper structural morphism; it also depends on this item. The new node asserts a conditional global restriction criterion, with none of those hypotheses and no claim of sheaf-valued exchange.
lem-sfb-closed-torsion-rigidity-serre-transfer vs prop-weil-pbc-gabber-pair-comparison: the existing node is classical torsion étale cohomology on an affine henselian pair; the new node is a conditional coefficient transfer on a qcqs scheme pair, not restricted to affine spectra or henselian pairs.
lem-sfb-closed-torsion-rigidity-serre-transfer vs lem-weil-pbc-condensed-constructible-serre: that node concerns kernels/cokernels/extensions of constructibles over a noetherian underlying space and finite-subextension-valued coefficients; it asserts no cohomology comparison and supplies neither this coefficient topology nor coproduct closure.

Blueprint searches: ancestor command returned det-sf-comp-coherence-cocycle. Whole-blueprint searches for henselian, henselization, rigidity, coefficient transfer and closed immersion and whole-DAG searches for the source, tags and concepts found no duplicate. The new nodes retain the full ancestry via this item and its four intervening ancestors; same_as is empty.

## Review by NA

I read the worker brief, stage-1 contract, three blueprint levels in SETUP, GOAL, both copies of delivery-errors B–E, the item's chapter and unit, and the current main-20261015 refinement proof. The unit record still has an older smooth-purity copy, while this item's ancestry and chapter are the supplied six-functors-basics refinement; I preserved those records and used only generic tools from other units, declaring them in split_report.tool_uses.

For the item and the new henselian ring node I read RTW Section 1.1, in particular Proposition 1.1.2 and its actual henselization argument and Corollary 1.1.5. Its proof identifies W with the henselization along W^c, which implies exactly the henselian-pair assertion of the new node. The statement specifies the idempotent definition of henselianity and makes no cohomology claim. The new coefficient-transfer node follows the ordinary ambient convention of the blueprint refinement, but no exact proof of it was present in the literature read. I checked HRS Lemma 5.3 and the uses of RTW Section 1.3: these do not by themselves give the proposed transfer with all-continuous Omega. Its missing source is therefore recorded as WANTED instead of attributed to those results. Its own statement is complete and contains no proof sketch.

Step 1 uses the actual quotient-spectrum homeomorphism and all clauses of the w-local component statement. Closedness of W^c is used to identify V(J), rather than assuming that an arbitrary set of maximal ideals is closed. Radicality is proved by intersection, and the reduced zero-dimensional local ring is a field with the original residue field. The existing component homeomorphism gives the extremal disconnectedness required by the definition. I checked that the residue fields need only be separably closed, not algebraically closed. This is a short ring/spectrum argument from the quoted statements, so it is elementary; no geometry child simply restates this clause of the item.

Step 2 uses the proper and closed-immersion base-change clauses of lem-weil-pbc-proper-fp-permanence, the definition of properness (finite type and separated), the affine qcqs lemma, the separated affine-open-intersection theorem and the converse affine-cover quasi-separatedness criterion. All apply over the affine bases W and C. In particular no absolute quasi-separatedness of Y is smuggled in, and no finite presentation is substituted for finite type.

Step 3 uses exactly the new henselian-pair statement, then applies sk-thm-pbc-henselian-h0 to the identity proper morphism of W. Its statement covers every sheaf of sets and explicitly includes abelian sheaves, so it supplies natural section restriction for G = R^r q_*F later; it is not being used as a higher-cohomology comparison.

Step 4 uses the projectivity clause of sk-thm-pe-weakly-contractible-basis on W and on the C established in Step 1. Lifting a section of a quotient sheaf by splitting its fibre over the representable proves exactness of evaluation. The abelian étale/pro-étale comparison states cohomology agreement without torsion or Noetherian hypotheses; I use its full abelian generality to get H^1 = 0 for the kernel of any étale epimorphism and thus exact étale sections. This comparison is not the narrower constructible finite-ring comparison node.

Step 5 uses thm-weil-pbc-bounded-below on the proper q and K = F[0], which has torsion cohomology for every locally torsion F. Exact inverse image commutes with cohomology by the quoted exact-functor theorem. The exact-global-sections Leray statement applies because Step 4 verified its finite-colimit preservation hypothesis for both bases. I also cite the bounded-below Leray isomorphism with functoriality: together with the counit definition of proper exchange and the natural degree-zero restriction of Step 3, these identify the displayed composite with the actual cohomology pullback. No uniform annihilator, cohomological dimension or finite presentation is used.

Step 6 uses exact module inverse image, its actual adjunction, preservation of small colimits by a left adjoint, the scalar-matrix pullback theorem for arbitrary condensed Lambda, and constructible preimages. The latter applies to the pulled-back finite locally closed strata; the former keeps their identical scalar presentations and pulled-back pro-étale covers. This works locally on affine opens as required by the arbitrary-scheme definition, so it does not require X to be qcqs. Applying minimality to the inverse-image class explicitly proves membership in P_T for the whole closure, including extensions and all coproducts. I deliberately did not cite lem-sfb-pullback-constant-model-constructible for Omega: its statement fixes the different finite-subextension-valued convention.

Step 7 checks every hypothesis of the new coefficient criterion against Steps 2, 5 and 6. This is where the open coefficient transfer is used; it is not concealed in an elementary argument or attributed to henselian degree zero. This generic tool has genuine classical hypotheses which the earlier steps prove, so the geometry and the classical torsion argument stay in the parent split.

Step 8 uses the weakly étale site-localization equivalence, exact internal/section-ring module reconstruction, and the ringed sheaf-slice derived comparison. The latter explicitly states that a K-injective representative remains K-injective on the slice for an arbitrary sheaf of commutative rings. It therefore applies to the reconstructed coefficient sheaf, not merely a constant discrete ring. The same evaluated complex computes the left side; the identical section unit and the module inverse-image composition identify the arrow and the target. This is an argument about the actual derived restriction in D(Ab), rather than unrelated degreewise isomorphisms. No new per-degree replacement node was created.

I opened the statement of every proof citation and placed its verbatim statement in citations.json. The proof dependencies are exactly the union of uses. Every step is shorter than 2000 characters. The two new nodes have no proof or proof dependencies; their mathematical search records come directly from searches.jsonl. In Mathlib I read the returned HenselianRing and CondensedMod.IsSolid definitions: these are notions, not the asserted pro-étale theorems. HenselianLocalRing implies a henselian maximal-ideal pair only in the local case, and is not a proof for arbitrary w-contractible rings. No search outage was converted to a negative result.

Small cases: R = 0 gives C = W = empty; J = 0 on a reduced zero-dimensional w-contractible ring gives the identity; a separably closed field gives the identity; a strictly henselian local ring gives its usual maximal-ideal pair, including positive-dimensional local spectra; nilpotent thickenings satisfy the coefficient criterion by site invariance; the zero coefficient ring and zero/rank-zero modules are harmless; characteristic ell is not excluded. For a closed point in a proper curve over a separably closed field, the relative transfer hypothesis is not automatic (finite-coefficient positive-degree cohomology obstructs it), so the new criterion is not claiming arbitrary closed restriction. The ambient HHL 7.15 counterexample does not satisfy a closed-pair torsion-rigidity hypothesis and does not justify extending the conclusion to all pro-étale modules. I found no counterexample to the two proposed new statements in these tests. No statement dispute or change is asserted.

Dry-run correction: removed the context-dependent phrase “the item’s” from Step 8 and explicitly named the evaluated site object. Also checked the Stacks tag index and corrected the labels in Steps 1 and 4 to 0968/lemma-spectral-split, 098F/lemma-w-contractible-proetale-cover and 099W/lemma-compare-cohomology. The statements and dependencies were unchanged by this correction.

Final citation audit: Step 8 now explicitly cites the Grothendieck property of ring-sheaf module categories and existence of K-injective resolutions. These supply the representative before applying the slice theorem; their complete statements are included in citations.json.
