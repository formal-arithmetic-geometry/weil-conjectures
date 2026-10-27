# Stage-1 report: lem-sfb-finite-square-zero-adic-thickening

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-square-zero-adic-thickening.json`: statement, split in two steps; no Mathlib match after recorded semantic, type-pattern and source searches.
- `citations.json`: one verbatim statement quotation for each of the two proof citations.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. The item statement, source, inherited search records and full blueprint ancestry are retained. Current searches are appended, not substituted for the earlier worker's records.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the exact blueprint id, Tag 0DYC, the source label, square-zero/nilpotent completeness, quotient completeness and `IsAdicComplete`. No declaration gives the item's assertion. The private nilpotent-completeness lemma in `RingTheory/ArtinianCoefficientEventualFlatness.lean:30` proves only the elementary prerequisite, not H-adic completeness from the quotient. Existing complete-local quotient results go in the other direction and require locality.

## WANTED

None. Both needed sources are available in `literature/stacks-project/algebra.tex`.

## Findings and statement audit

The current statement is correct. Its existing source correctly identifies Tag 0DYC, label `lemma-complete-modulo-nilpotent`, lines 23215-23236. That source assumes completeness for I and completeness of A/I for J; with I=Q and J=H, the only extra verification is Q-adic completeness. Q squared zero supplies this from the defining inverse limit, without Noetherianity. The Noetherian hypothesis is used exactly in the cited two-ideal theorem. The title/id's word "finite" introduces no further finite-module or finite-algebra hypothesis in the actual statement, and none is used.

An existing DAG node already states the more general two-ideal theorem: `lem-sfb-two-ideal-adic-completeness`. It has the same chapter and unit as this item and is unmerged. Reusing its statement avoids creating another node for the item's own clause. Searches for 0DYC and the source label also found uses in the parent deformation nodes and `lem-weil-pbc-power-series-complete-over-complete-base`; these are applications, not replacement statements for this item. Whole-blueprint searches for 0DYC, square-zero, adically complete and nilpotent found no equivalent imported blueprint assertion. The latest blueprint's `det-thm-sf-ctf-stability-direct-images` proof (3) is the remote ancestor route already described by this item's long `blueprint.from.place`; no route change is proposed. `tools/blueprint_refs.py ancestor` reports `None` on the inherited created-node chain, so the existing null `from.node` and complete via list are retained, with an explicit split-report explanation.

## Not duplicates

No new nodes. The possibly duplicated fact is reused directly as `lem-sfb-two-ideal-adic-completeness`; the square-zero constant-tail observation is an elementary step, not a node.

## Review by Q27

I read the entire statement and proof of Stacks Tag 0DYC in `algebra.tex:23215-23236`, and the definition of adic completeness in `def-weil-pbc-adically-complete-ring`. I also opened the Noetherian-ring definition and the complete statement of `lem-sfb-two-ideal-adic-completeness`. The latter says exactly that a Noetherian R complete for I, with R/I complete for the image of J, is J-adically complete; it does not require a split extension, a flat coefficient algebra, or a local ring. There are no new-node sources to audit.

Step 1 uses only the cited inverse-limit definition. Because Q^2=0, every Q^n for n at least two vanishes, and all later transition maps are identities. I wrote both reconstruction of a compatible family from its second coordinate and its uniqueness. This proves bijectivity of the canonical map, including separatedness, rather than merely existence of Cauchy limits. The quotation in citations.json is copied verbatim from that definition's statement.

Step 2 uses only the statement of the existing two-ideal lemma. Substitution R=C, I=Q, J=H preserves all hypotheses: C is Noetherian by assumption, Q-completeness is step 1, and the image ideal (Q+H)/Q equals the assumed (H+Q)/Q by commutativity of ideal addition. The conclusion is exactly H-completeness, and no content from the lemma's proof is used. Its complete statement is copied verbatim into citations.json. Its unit is the item's unit, so no off-route tool declaration is needed.

For small cases I checked Q=0 (the criterion reduces to the original completeness assumption), H=0 (the quotient systems are constant from positive level), H=C (quotient completeness forces C/Q=0, hence C=Q and 1 in Q^2 forces C=0), and the zero ring. For a nontrivial square-zero example C=k[[t]][epsilon]/(epsilon^2), Q=(epsilon), H=(t), the hypotheses and predicted completeness hold; for C=k[t,epsilon]/(epsilon^2), the t-adic completeness assumption fails, as it should. No hypothesis or conclusion correction is necessary.

I checked delivery-errors B--E against the files: no unsplit node containing a proof, no new notion without its definition, no relabelled clause, no extra source-only non-elementary citation, no use of a cited node's proof or a definition in place of a theorem, no hidden change of coefficient category, and no long proof step (both steps are below 2000 characters). The split's sole non-elementary inference is explicitly cited. Actual Mathlib searches used two semantic phrasings and two source patterns; all services returned results. I read Basic.lean:42-56 and 710-737, RingHom.lean:34-56, and Exactness.lean:85-111 to reject the nearest candidates: the lift results assume a complete target, and completion flatness/exactness do not state this quotient criterion. Inherited searches are clearly distinguished from this run's appended searches.

## Unfinished work

None in this split. The existing two-ideal lemma remains its own stage-1 item; its proof is not duplicated here. The required server dry run exited 0 and printed OK (not pushed) at 56280510107: preflight passed. This included the server DAG and split checks. The delivery command is run only after that dry-run process has exited.
