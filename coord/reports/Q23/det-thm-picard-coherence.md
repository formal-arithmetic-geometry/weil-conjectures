# Q23: det-thm-picard-coherence

## Files written

- dag/nodes/sec-picard-framework/det-thm-picard-coherence.json: statement item split into five assembly steps; no Mathlib match for the combined theorem.
- citations.json: eleven entries copying the cited statements verbatim, indexed by proof step.
- report.md; searches.jsonl is the unedited search-command log.

No new nodes and no Mathlib leaves. Only the sandbox is written; no Lean, compiler, Lake, repository git commands, or agents were used.

## Attachments

None claimed. The blueprint tag det-thm-picard-coherence is absent from WeilConjectures. I searched the named higherDirectImage, base-change and perfect-direct-image declarations and read FiniteFreeComplex.lean, Sections.lean, PerfectBaseChange.lean, RelativelyFlatCanonicalModuleBaseChange.lean and NoetherianPerfectDirectImage.lean. Several clauses have project declarations, but the PerfectBaseChange declaration explicitly supplies cohomology-level complexes and an affine/noetherian Cech assertion rather than the entire item. This is no basis for an ATTACH of all clauses. Existing DAG statements are used as statements, independently of their implementation status.

## WANTED

None. The current blueprint and Stacks sources are present.

## Corrections and source audit

The statement is unchanged. The imported paragraph was not a checked split: it cited Cech and projective-space statements for general proper coherence, asserted approximation and complex shortening without naming the already available intermediate theorems, and mixed a local cohomology model with a derived representative. I replaced that paragraph by an assembly using the live statements of lem-pc-rf-perfect-base-change, lem-pc-universal-finite-free-complex and lem-pc-coherent-hi. This retains the unit's local-complex route. In particular the universal finite free complex is only used for its stated cohomology isomorphisms; the proof never upgrades those unspecified isomorphisms to a quasi-isomorphism with Rf_*F.

The current blueprint refers to clause (3) of lem-pc-rf-perfect-base-change. Its maintained live DAG statement is the more general global proper-flat theorem, whereas blueprint_update records the new affine/Cech formulation. I read both and used the live statement, as required. Stacks perfect.tex, Tag 0B91(2), lemma-flat-proper-perfect-direct-image-general, explicitly gives exactly the global perfectness and arbitrary base-change assertion for the relatively flat finitely presented module. No assumption that f itself is flat is imposed.

The historical sk-thm-picard-coherence has related conclusions but also asserts a fibre-dimension bound; the present item merely uses a finite complex length bound. Neither it nor the proper noetherian coherence node states precisely the entire item, so blueprint.same_as is empty. The local finite-complex, noetherian coherence, and base-change nodes found by DAG/blueprint searches are reused. No new clause nodes are created. The optional counterexamples and fibre-dimension sharpening in the imported proof are not needed to prove its statement.

## Not duplicates

No new node pairs. Existing lem-pc-coherent-hi handles proper coherence; lem-pc-universal-finite-free-complex handles universal local complexes; lem-pc-rf-perfect-base-change handles canonical derived base change and perfectness. Each was opened and its statement, rather than its proof, checked.

## Review by Q23

I read the chapter and sk-thm-picard-perfect unit records, the latest chapter and perfect-locus proof, and both latest files for this item. The item is an auxiliary local-complex input, not the unit's key statement, so no unit realization record needs changing. For literature I read coherent.tex at Tag 02O5, proposition-proper-pushforward-coherent, and Tag 01XZ, lemma-coherent-Noetherian; modules.tex at Tag 01BO, lemma-finite-presentation-quasi-coherent; and perfect.tex at Tag 0B91(2), lemma-flat-proper-perfect-direct-image-general, and Tag 08EB, lemma-perfect-affine. No new-node source review is needed because there are no new nodes.

Step 1 uses the exact live statement of lem-pc-rf-perfect-base-change: it specifies the canonical module comparison and arbitrary base change. The proper, finite-presentation and relative-flatness hypotheses coincide with the item. I did not use a bare isomorphism of objects to infer that a specified map is invertible.

Step 2 uses the exact live statement of lem-pc-universal-finite-free-complex, with its base-change quantifier, support [0,d], and noncanonical cohomology isomorphisms. Taking the identity base change identifies the higher direct image on U. Computing cycles at a zero term proves the needed vanishing. No fibre-dimension theorem or Nakayama lemma is hidden in that argument.

Step 3 checks every hypothesis of the proper coherence theorem before applying it. pqf-lem-proper-basic gives finite type; pqf-lem-locnoeth-lft gives locally Noetherian X. Clause (0) of lem-weil-pbc-quasi-coherent-finite-type-affine gives quasi-coherence of the finitely presented sheaf, and the actual finite-presentation definition gives its finite type by the images of the target basis vectors. pqf-lem-coherent-ft-locnoeth therefore gives coherence of F. The statement of lem-pc-coherent-hi then gives coherent R^qf_*F for every q. Relative flatness is never used in this step, so the stronger assertion in (b) is proved. The flatness and finite-presentation notions are the sheaf notions, not finite presentation of an ordinary stalk module substituted for the sheaf condition.

Step 4 gets perfectness from the live proper-flat theorem. def-pc-perfect-complex explicitly includes the affine description by a bounded finite-projective complex. I opened lem-sc-principal-open-finite-projective-tilde: it allows the entire spectrum as U and asks for finite projective localizations on every principal open. The splitting inclusion/retraction of each finite-projective term localizes to such a splitting, verifying this hypothesis; the conclusion is finite local freeness of each associated sheaf. Thus the asserted derived representative has the right terms. This does not assume that cohomology sheaves of a non-noetherian perfect complex are coherent.

Step 5 has no external theorem beyond the definitions of quasi-compactness and a sheaf. I wrote the finite subcover, its maximum bound, and the equality of sections from their restrictions. The empty scheme has the empty cover and bound zero. I also checked F=0, the identity morphism, finite morphisms, and a non-quasi-compact disjoint union of projective spaces: none invalidates a local bound, and a global bound is only asserted with quasi-compact T. Nonflat F is used only for noetherian coherence, not arbitrary base change or perfectness.

Against delivery-errors B–E: the existing definitions cover the statement's notions; no new statement or unsupported new lemma is introduced; all eleven uses have verbatim citation entries; there is no dependency path from the reused three major lemmas back to the item; elementary steps are written out; no claim is taken from the proof of a cited node. Every non-elementary step is under 2000 characters. Off-unit tools are declared in split_report.tool_uses, with the local-complex theorem explicitly demanded by the item and the other uses generic. No SGA is cited.

All Mathlib queries were run through msearch.py, and the returned hits were read. The first Loogle query reported unknown identifier AlgebraicGeometry, which is recorded as unavailable, not evidence of absence; the second query for the substring higherDirectImage succeeded with zero hits. Two semantic phrasings returned flat/proper morphism definitions, module pushforward, abelian structures and finite-presentation data, not the item. LeanSearch returned properness/base-change instances, and the AlgebraicGeometry grep returned no higherDirectImage or proper-coherence result. These are not matches to the combined theorem.

## Unfinished work

None in the stage-1 split. The cited existing nodes retain their own work and status. Required server dry-run and delivery results are recorded below after execution.
