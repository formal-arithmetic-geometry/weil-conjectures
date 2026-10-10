Files written:

- `dag/nodes/sec-abelian-varieties/def-sp-convergence.json`: item split in place; no new nodes; Mathlib searches found no exact match.

Attachments:

- None. No sorry-free declaration under `WeilConjectures/` states the exact-couple convergence definition.

WANTED:

- `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/def-sp-convergence.md` is referenced by the imported node but is not present in this checkout; the imported node statement itself was used as the source text.

What was wrong or incomplete in the imported node:

- Its `status` was still `imported`, with no stage-1 split metadata. I changed it to `split`, filled the blueprint provenance and `same_as`, and recorded the required Mathlib searches. The statement and dependencies were already complete, so no child node is justified.

## Repair of returned points

- **E (definition):** The former abutment sentence did not define the object or the comparison maps. I replaced it with the colimit $A^n=\\operatorname{colim}_{p\\to-\\infty}D^{p,n-p}$ along $\\alpha$, the image filtration $F^pA^n$, the map induced by $g$ to $E_\\infty$, and the filtration map to $\\operatorname{gr}^pA^{p+q}$. Weak convergence now means these maps are onto with the same kernel; abutting adds exhaustive and separated filtration; convergence adds regularity and the inverse-limit completeness condition.
- **E (consumer terminology):** I added the definition of boundedness (finitely many nonzero $E_2^{p,q}$ in each total degree) and explicitly defined weakly converges, abuts to, and converges to, citing Stacks Tags 012U and 0130.
- **E7:** The statement changed because the prior clause left the limit object, filtration, and comparison maps unrelated and omitted terms used by consumers; this reason is recorded here and in `split_report.summary`.

## Review by E1

I read the item dependencies `[def-sp-exact-couple]` and `[def-sp-filtration]` and verified that the former supplies $\\alpha$ and $g$, while the latter supplies induced filtrations, graded pieces, and the meanings of exhaustive and separated. I read Stacks Definitions 12.20.1 (Tag 011N), 12.24.9 (Tag 012U), and 12.25.2 (Tag 0130) to check the recursion, boundedness, weak convergence, abutting, and convergence clauses. I also read `WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`; its first-quadrant `Abutment` is not this exact-couple definition. The new colimit and image-filtration clauses make the source and target of both comparison maps explicit, and the same-kernel/onto condition gives the stated associated-graded isomorphism. I checked the page-2 boundary case $Z_2=E_2$, $B_2=0$, and the zero-page case. No proof steps or child nodes are needed for this definition, so `citations.json` remains empty. The returned definition and terminology faults are corrected above.

What could not be finished:

- The referenced blueprint markdown file is absent from this repository; no external download was attempted under the stage-1 rules.

## Second reading by E1

- Item statement: checked against the imported blueprint node and dependency statements `[def-sp-exact-couple]` and `[def-sp-filtration]`; the recursion, regularity, completeness, and abutment clauses agree with the available imported source.
- Proof steps: none; this is a definition, so there are no omitted dependencies or elementary proof claims to audit.
- New nodes: none; the repository-wide node search found no duplicate definition, and the Mathlib searches recorded above found no matching declaration.
- Boundary cases: at page 2, $Z_2=E_2$ and $B_2=0$; for a zero page all later pages and the abutment are zero; regularity and completeness remain independent conditions.
- Source availability: the source path named by the imported node is absent in this checkout, and the local literature directory contains only citation indexes, so the imported statement was the only available blueprint text.
- No mathematical changes were needed: the item is already a statement-only definition whose dependency references supply the exact-couple and filtration context.

### Corrections from the second reading

- Source check: Stacks Tag 011N defines spectral sequences, and Tag 012U defines weak convergence, abutting, and convergence; the local checkout has no Stacks `.tex`, so I checked the tagged source pages directly. Tag 0130 is a double-complex lemma, not a convergence definition, so it was removed from `source.external` and from the explanatory sentence.
- Regularity check: Stacks distinguishes regularity (eventual stabilization of each $Z_r^{p,q}$) from coregularity (eventual stabilization of each $B_r^{p,q}$); the statement now uses the former.
- Dependency and boundary check: `[def-sp-exact-couple]` supplies the page recursion and maps, `[def-sp-filtration]` supplies graded pieces and separated/exhaustive terminology; the page-2 and zero-page cases remain well-typed and unchanged.
