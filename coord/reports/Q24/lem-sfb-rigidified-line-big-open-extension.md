# Stage-1 delivery: lem-sfb-rigidified-line-big-open-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rigidified-line-big-open-extension.json`: statement, split in ten steps, not a Mathlib leaf. The mathematical statement is unchanged. Imported doubled TeX backslashes were normalized; definition dependencies for local-ring dimension, stalks, base change and closed immersions were supplied.
- No new nodes and no new Mathlib leaves.
- `citations.json`: 26 verbatim statement quotations, one for each step/dependency pair.
- `searches.jsonl`: five actual Q24 msearch calls (LeanFinder twice, Loogle, grep, LeanSearch). Existing upstream searches remain in the node as inherited history; the new entries correspond to this sandbox log.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for rigidification, codimension-one and line-extension terminology. The rigidification results returned there concern Artin–Schreier sheaves and other unrelated constructions; no declaration states this entire extension result. No sorry declaration was treated as an attachment.

## Sources wanted

WANTED: Moret-Bailly, *Pinceaux de varietes abeliennes*, Asterisque 129 (1985), II 3.2.2--3.2.3, for lem-sfb-rigidified-line-big-open-extension.

WANTED: Deligne, *Le lemme de Gabber*, Asterisque 127 (1985), Section 4.2, printed p.142, for the original regular-base comparison mentioned by the imported source record.

Neither PDF is present in this read clone. I did not download or claim to read either. The proof is explicitly an agent assembly from the available Stacks sources, following the regular-trait/spreading route specified by the imported item. Read `divisors.tex` Tag 0BD9, `algebra.tex` Tag 00PD, `limits.tex` Tags 0B8W and 01ZR, the local-ring neighbourhood-limit argument in Tag 0GWT, `topology.tex` Tag 0052, `schemes.tex` Tag 01IS, and `sites.tex` Tag 04TR. These are cited by tag and label, not by unstable section number. No SGA source is used.

## Corrections and route

The live item was unsplit and had no repair note. There was no earlier sandbox node, proof, report or search log to resume. The statement is mathematically sound as given; no STATEMENT-DISPUTED correction is needed. Its source is absent, so the new argument is not presented as a transcription of Moret-Bailly. The inherited source and blueprint chain are preserved. The current latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), and the unit/chapter records were read: this is a supporting geometric input on that inherited direct-image route, not a replacement of a unit step. `blueprint_refs.py ancestor` returns None for this agent-created chain; the inherited null `from.node` and full `via` list are retained. Searches of the whole imported blueprint for rigidified lines, line bundles, reflexive sheaves and codimension found no blueprint statement equal to this item.

The delicate inference is not that the regular locus of a normal Noetherian scheme is open; no such inference is made. It is that a line over a local trait descends to some base neighbourhood, and that its prescribed generic comparison descends separately on the inverse system of overlaps with U. Also, local extensions need not agree over arbitrary singular overlaps. The construction first isolates the relevant boundary components, making the distinct chosen neighbourhoods intersect only in U, where the given line supplies all comparisons.

## Not duplicates

No new nodes were created. Existing general results were reused, including `lem-sfb-smooth-dvr-generic-line-extension`, `lem-trf-invertible-affine-limit-descent`, and `lem-trf-fp-module-limit-isomorphism-descent`. The stronger regular-base rigidified-line extension was read but is not applied to a normal base. No new node is an item clause, an elementary step, or a duplicate of these results.

## Review by Q24

I checked the mathematical statement against the imported regular-trait formulation, including preservation of the specified identity rigidification and inclusion of every local-ring-dimension-one point. Since the original Moret-Bailly text is unavailable, the correctness of the assembly rests on the following explicit Stacks argument, not on an unverified attribution. All cited node statements were opened; `citations.json` copies their actual text, including some full multi-clause statements so the hypotheses remain visible.

1. Step 1 uses scheme sobriety only for a generic point, the generalization-chain dimension theorem for the dimension-zero assertion, and the normal-dimension-one DVR theorem with all its hypotheses in force: S is locally Noetherian, integral and normal. The DVR has fraction field k(eta), and U pulls back to exactly its generic point, because the closed point s is outside U. I also cited the affine-open Noetherian and affine-stalk localization statements explicitly, and wrote the ideal-contraction argument showing that this stalk is Noetherian. There is no completeness, excellence or residue-characteristic assumption.
2. Step 2 uses the affine-open Noetherian theorem, finite components of a closed subset, sobriety for those components, the dimension-chain theorem, and the affine-neighbourhood basis in the local-ring-limit node. The cited finite-component statement applies to the closed boundary in a Noetherian affine chart, not to an arbitrary non-Noetherian global space. The two-step chain rules out a different component generic point above s. Removing finitely many other components is an actual open shrink, and choosing an affine subneighbourhood is licensed by the cited basis statement.
3. Step 3 uses both clauses of the local-ring-limit statement that supply directedness and affine transitions, and the scheme-over-limit statement, applied twice. In the second application the scheme over the fixed affine base is the whole overlap G_(U intersect A_s), not an incorrectly changed generic fibre. Its limit is G_K because of Step 1. Restricting to neighbourhoods inside a fixed affine is a cofinal tail. The collection of affine opens is a set, so the descent indices are small.
4. Step 4 checks every qcqs hypothesis required later. Finite presentation implies finite type from the stated algebra presentations and quasi-compactness; separated finite type survives arbitrary base change by `lem-pod-separated-finite-type-base-change`. The cited finite-type-over-Noetherian theorem makes G_W Noetherian; the open-immersion qc theorem gives quasi-compactness of its overlap with G_U. Locally Noetherian quasi-separatedness applies to both systems, including that open. These are precisely the statements quoted, with no properness or affine-intersection assumption inserted.
5. Step 5 applies the smooth base-change clause of `lem-pc-proper-base-change` and the whole statement of `lem-sfb-smooth-dvr-generic-line-extension`: a smooth finite-type scheme over a DVR, with no demand for geometrically integral fibres or properness. Then the existing invertible affine-limit descent theorem applies to the first small qcqs system with affine transitions. It supplies an actual line model and a comparison to the trait line, not just a Picard class.
6. Step 6 uses the precise fixed-model isomorphism descent statement `lem-trf-fp-module-limit-isomorphism-descent`, whose conclusion includes an inverse and the equations identifying the lifted map with the specified limit map. Its two models are restrictions of H and N to the fixed overlap stage. Lines are finitely presented since locally they are O. Step 4 checks the overlap stages, which need not be affine. This is stronger than object descent and is necessary to compare with the original N on the whole shrunken overlap.
7. Step 7 is an elementary rank-one construction. Pullback of a rank-one basis verifies invertibility of D_s and M_s. The explicit formula for beta_s, and evaluation after pulling it to the identity, verify the original rigidification r, not merely existence of some normalization. No extension of an arbitrary unit function is asserted.
8. Step 8 is a short topological calculation from the already cited dimension-chain theorem. If two distinct boundary neighbourhoods met in Z, their two generic points would lie in a strict chain s,t,eta. This contradicts height one. I kept this as an elementary step, not a redundant new node. It does not assert that the neighbourhoods are disjoint inside U.
9. Step 9 invokes the existing effective module-sheaf gluing statement on the Zariski site. The covering is set-indexed, all comparisons are defined on the actual overlaps, equal-index maps are identities, and the displayed cancellation verifies every triple cocycle. Local freeness of rank one is local, so the descended module is invertible. This is a citation of the statement of the gluing node, not its construction or an unrelated full-faithfulness assertion.
10. Step 10 glues compatible local maps and inverses of sheaves on V, giving an isomorphism along the identity. Their compatibility follows from the explicit normalization and comparisons through N. The maps agree with r on U by construction. The inclusion of all points of dimension at most one is exactly what Steps 1 and 2 arranged.

The generic geometric tools belonging to other units are declared in `split_report.tool_uses`, with the reason for each. They are general statements about Noetherian schemes, limits and sheaf descent; none substitutes a different high-level route for the unit's direct-image proof. No top-level tool approval field was written.

I tested the construction on U=S (empty T and no extra gluing), a field base (all of S already lies in U), a DVR base with U its generic point (the trait theorem directly supplies the missing line), a normal surface with two intersecting boundary components (remove their intersection from the two neighbourhoods, then glue through U), and a locally Noetherian non-quasi-compact base (work independently on set-many affine neighbourhoods and apply unrestricted open-cover gluing). In particular the proof requires neither a globally finite boundary nor a globally Noetherian base. It also works with relative dimension zero; the connected-fibre and commutative-group hypotheses are retained, although this existence argument only uses smoothness, finite presentation and the identity section.

The B--E checklist was read in full, including its duplicate copy: no new nodes require B1/B2 or Mathlib-leaf audits; all imported mathematical content was retained, TeX formatting repaired, every non-elementary assertion is assigned a cited statement, and the elementary normalization, overlap and sheaf-map arguments are written out. No proof step exceeds 2000 characters (largest is 1167), and no long inline sublemma is hidden. No circular dependency or appeal to a theorem's unstated proof data is intended; the server checks below verify the DAG mechanically.

## Unfinished work

None in the stage-1 split. The wanted original literature is explicitly recorded above. Stage 2, Lean writing and compilation are outside this delivery.

## Validation

Server check_dag passed with no introduced finding. Server review_split passed with zero new nodes. The first full delivery dry run passed at 0ae8d318d22; a final pass follows the added explicit affine-stalk citation. No check_dag, review_split or preflight script was run locally, and no compiler, Lake command or git command was run in the shared repository.
