## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-completion-isomorphism-local-invariants.json`: item split into four proof steps, statement unchanged, no Mathlib match for the combined assertion.
- `citations.json`: five verbatim cited-statement quotes, one for every use in every step.
- `report.md`: this report. `searches.jsonl` is the unmodified log produced by msearch.py.

## New nodes

None. Existing Mathlib leaves already supply every non-elementary input. No new Mathlib leaves.

## Attachments

None. Searched the entire project `lean/WeilConjectures/` for the exact blueprint id, completion/local-invariant terminology and completed local isomorphisms. No project declaration states all the clauses from the given hypotheses. `RingHom.completion_map_bijective` in `WeilConjectures/RingTheory/CompletionMapBijective.lean` goes in the converse direction and assumes flatness, residue bijectivity and equality of maximal ideals; it is not an attachment for this item.

## WANTED

None. The needed Stacks sources are present locally.

## Findings and corrections

The imported statement is correct; no statement dispute or statement correction was needed. It was statement-only, with no proof to preserve. There was no previous sandbox item or report. I copied the current repository item, preserved its provenance and historical searches, and added the explicit argument. Tag 0CAV does not literally state this algebraic lemma: it is the local-invariants subargument used by the parent's completed-stalk criterion. The report and proof_origin identify the argument as an agent assembly of the actual Stacks results, rather than attributing a nonexistent verbatim lemma to 0CAV.

The current blueprint ancestor is `lem-trf-local-term-locality`. I read its proof in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`, the current chapter/unit records, and the parent `lem-trf-completed-stalk-isomorphism-etale`. The newest blueprint itself discusses contracting correspondences and does not state this local algebra assertion. This item is an existing refinement on its inherited nodal-model/approximation branch; I retained that provenance and did not change a unit or chapter route. `blueprint.from.place` was already specific, and remains so; `same_as` was checked and remains empty. Searches `tools/blueprint_refs.py search completion`, `search 'maximal ideal completion'`, and `search 'completion isomorphism'` found no exact blueprint statement to reuse as the item. The last two returned zero matches; the broad first search had many unrelated coefficient-completion nodes.

## Search results read

For the item I ran the required msearch.py commands under Q58 with leanfinder (two different natural-language formulations), loogle `AdicCompletion, IsLocalRing.maximalIdeal`, grep `maximalIdeal_eq_map|residueField_map_bijective|pow_smul_top_eq_ker_eval` in `RingTheory/AdicCompletion`, and leansearch about all positive-power quotients. Every service answered, and all five exact queries and their returned metadata are appended to mathlib_searches from the actual searches.jsonl. Historical searches from the repository remain intact.

The first LeanFinder search returned local/completeness criteria, complete-ring equivalences and finite quotients with additional assumptions. The second returned formally unramified criteria and surjectivity-on-stalks residue maps. I read `Mathlib/RingTheory/Unramified/LocalRing.lean`; those results require essential finite type/formal unramifiedness or the very ideal equality to be established, and do not prove this item directly. LeanSearch returned completion constructions, liftRingHom coordinate formulas and completion/tensor equivalences, not the combined assertion. Loogle and grep located the actual local-completion and projection-kernel facts. I read LocalRing.lean lines 79-107, Completeness.lean around 155, and LocalRing/Module.lean around 72. They confirm the already-existing leaves, not a one-line specialization proving all clauses of the item. Searches of the DAG by completion, maximal ideal, quotients, the relevant Stacks tags and Nakayama identified the exact ring projection node `lem-weil-pbc-adic-completion-mod-power`; I used it instead of the more general module-completion node considered during discovery.

## Not duplicates

No new node is created. Reused `lem-weil-pbc-local-completion-local-ring`, `lem-weil-pbc-adic-completion-mod-power`, `lem-weil-pbc-nakayama-local-generators`, and the Noetherian definition. The existing `lem-weil-pbc-flat-local-completion-iso` and its bijectivity refinement are converse-direction results and need flatness. The module-completion kernel result generalizes the chosen projection node but need not be cited in addition to it.

## Review by Q58

I read the actual source in `literature/stacks-project/more-morphisms.tex`, Tag 0CAV, label lemma-isomorphism-approximation, lines 11071-11142, especially its first proof paragraph and its quotient-power discussion. I also read `algebra.tex` Tag 05GG, label lemma-hathat-finitely-generated, lines 22645ff.; Tag 05GI, label lemma-radical-completion, lines 22734ff.; and Tag 00DV, label lemma-NAK, lines 3616ff., including (4). The tags were checked against tags/tags. The proof_origin is agent because this is the explicit assembly of these statements, not a transcription of a single printed proof. No SGA source is used.

Step 1 cites the full statement of `lem-weil-pbc-local-completion-local-ring`, which I opened. It supplies locality of both completions, the extended maximal ideals, their description as projection kernels and the unit criterion. Both input rings are Noetherian and local, as required. The step proves, rather than assumes, that the isomorphism carries these ideals onto one another: it and its inverse preserve units. Finite sums of products prove the assertion for powers. This is not a new lemma to split off and not a clause moved into a new node.

Step 2 cites `def-weil-pbc-noetherian-ring`, whose actual statement is every ideal is finitely generated, and `lem-weil-pbc-adic-completion-mod-power`, whose actual statement gives surjectivity, the canonical composite, and the kernel for every positive power. I checked those exact clauses; the weaker mod-ideal node would not suffice. Finite generation holds for each maximal ideal without any excellence, flatness, finite-type, domain or completeness hypothesis on the input rings. The identification of powers of the extended ideal with extensions of powers is written as the finite-product expansion. No additional commutative-algebra theorem is hidden there.

Step 3 is elementary from the previous steps. Both quotient identifications come from the specified projections and their computed kernels. The inverse is induced by h inverse. Checking on the class of an arbitrary a shows the resulting map is exactly [a] mapped to [phi(a)], not merely some abstract quotient-ring isomorphism. The equation with projections is also the defining coordinate equation of h. Thus n=1 is the actual residue-field map. This step needs no independent non-elementary input.

Step 4 cites the Noetherian definition and the actual submodule clause of `lem-weil-pbc-nakayama-local-generators`; I read both statements. For b in m_B, surjectivity modulo m_B squared gives a with phi(a) congruent to b; locality forces a into m_A. Thus J+m_B squared=m_B. Apply Nakayama with base B, finite module M=m_B and submodule N=J. Finiteness is exactly Noetherianity of B; locality is assumed; m_B M=m_B squared by ideal multiplication. All the hypotheses of the cited submodule theorem are established before applying it. In particular this does not assume B is a finite A-module or phi is surjective.

Against delivery-errors B: there are no new nodes, so no statement-only/proof-sketch or duplicate-node problem arises; the existing statement introduces both rings and maps, defines locality and ideal extension inline, and cites its two definitions. TeX is singly escaped in the underlying strings. Against C: every non-elementary fact is furnished by the cited node's statement, not its proof, and citations.json contains literal substrings I checked against those open files. The inputs are already Mathlib leaves, so the different chapter/unit of these generic algebra tools does not change the geometric route. Against D: all four steps carry the argument in the item; no relabelling node, moved conclusion or circular induction is introduced. Against E: the only finiteness needed is finite generation of the maximal ideals, and every use is identified above. Each step is under 700 characters, so none reaches the long-step threshold or hides a separately parameterized comparison lemma.

I tested the statement on fields (m=0; every positive quotient and completion is the field itself), the identity of a Noetherian local ring, the completion map Z_(p) to Z_p (the original map need not be onto), and the identity of k[epsilon]/(epsilon squared) (nilpotent maximal ideal; higher powers vanish). The local map k[[t]] to k[[t]], t mapped to t squared, has injective but nonsurjective completed map; its quotient modulo the square is not onto and the extended ideal is (t squared), so it correctly fails the essential hypothesis. These cases also check why the final equality requires the n=2 comparison and Nakayama, rather than residue-field equality alone. The statement excludes the zero ring and requires n at least 1; no boundary case was silently discarded.

No work remains mathematically. Server validation and delivery are recorded below after their actual results.

## Validation

On 2026-10-23, the required server dry run `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q58 lem-trf-completion-isomorphism-local-invariants --no-push` exited 0 and printed `OK (not pushed)` at 2d7929024a8: preflight passed. No diagnostics required repair. This report-only validation entry is followed by a final dry run and the authorized direct push. No Lean was written and no compiler, Lake or build tool was run.
