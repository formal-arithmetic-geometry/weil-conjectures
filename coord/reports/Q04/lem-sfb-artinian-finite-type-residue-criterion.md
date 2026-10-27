# Stage-1 delivery: lem-sfb-artinian-finite-type-residue-criterion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-artinian-finite-type-residue-criterion.json`: existing statement, now split in five steps; no statement change; no Mathlib match for the complete item.
- `citations.json`: ten verbatim statement quotations covering every citation in the five steps.
- `report.md`: this report.
- `searches.jsonl`: actual searches recorded by the required msearch.py command.

New nodes: 0. New Mathlib leaves: 0. Four existing statement leaves are reused: Artinian finiteness from the radical quotient, all-affine-pairs finite-type criterion, pointwise finite-type criterion, and uniqueness of the prime of an Artinian local ring.

## Attachments

None. I searched `lean/WeilConjectures/` by the item's blueprint tag and by Artinian, finite type and residue terminology, and read `WeilConjectures/RingTheory/ArtinianLocalEssentiallyFiniteTypeResidue.lean`. Its `RingHom.essFiniteType_of_artinian_local_residue` proves essential finite type, not the ordinary finite-type conclusion here. It is not an attachment for this item. The nearby `Sheaf/RingTheory/IsolatedPrimeResidueFinite.lean` has a different field-base isolated-prime statement and its proof is sorry.

## WANTED

None. All sources used are present in the read clone.

## Corrections and findings

The statement agrees with Stacks Algebra Tag 07DT, part (2), and with the affine-target specialization of Morphisms Tag 02HV. It is neither disputed nor weakened. The original empty proof is replaced by a complete assembly of existing facts.

I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, especially (3), as well as the recorded chapter and unit. This is the local commutative-algebra prerequisite reached through the inherited alteration/versal-neighbourhood chain, not a replacement of the six-functor route. The inherited blueprint provenance has a null ancestor id: the read-only `blueprint_refs.py ancestor` command reports None. Its existing specific place and via list are retained; `same_as` is [] after the whole-blueprint searches. The direct-images blueprint file identifies its node as `det-thm-sf-ctf-stability-direct-images`.

The existing Artinian finiteness leaf already supplies the real input to 07DT (1). Introducing a separate node for 07DT (2), for finite-type descent to the residue field, or for adjoining a finite module generating set would merely duplicate or restate this item or create elementary nodes. None was created.

## Searches and Mathlib verdict

The item's earlier search records are retained. Fresh searches were run with msearch.py, and their actual queries and results are recorded in the item and searches.jsonl. LeanFinder's new phrasing found `IsSemiprimaryRing.finite_of_isArtinian`, whose source I read at `Mathlib/RingTheory/HopkinsLevitzki.lean:78-98`; this is the existing leaf `lem-weil-pbc-artinian-finite-over-residue-finite`, not a direct match for the item's finite-type criterion. LeanSearch's second phrasing found module-finiteness results that assume finite type, finite-length results and essential-finite-type results. Loogle found two quasi-finite-fibre results already assuming finite type. The RingTheory grep found essential-finite-type or quasi-finite-fibre results, not the ordinary finite-type converse. A supplementary finite-type morphology grep was exploratory; no new node or match is based on it. No unavailable service was reported as an absence.

Whole-DAG searches by tags 07DT and 02HV and by Artinian/finiteness terminology identified the reused Artinian finiteness leaf and the distinct essential-finite-type node. Whole-blueprint searches included Artinian, finite type, and finite type is checked. I read the precise existing statements of all cited nodes before writing the proof and copied their statements, or the full relevant implication, to citations.json.

## Not duplicates

There are no new nodes to compare. `lem-weil-pbc-artinian-local-essentially-finite-type-residue` proves the converse for essentially finite type only, whereas the item proves the equivalence for ordinary finite type. `lem-weil-pbc-finite-type-lift-nilpotent` has a nilpotent ideal in the base and is not needed here. The existing `lem-weil-pbc-artinian-finite-over-residue-finite` is cited instead of recreated.

## Review by Q04

I read Stacks `algebra.tex`, lemma-essentially-of-finite-type-into-artinian-local (07DT), including the proof of (1) and (2), and `morphisms.tex`, lemma-artinian-finite-type (02HV). For the scheme translation I also read definition-finite-type (01T1) and lemma-locally-finite-type-characterize (01T2). No new nodes require additional sources. The source's lifting of algebra generators followed by module-finiteness is written explicitly, rather than treating 07DT (2) as a new black box.

Step 1 uses exactly the polynomial-expression definition in `def-weil-pbc-finite-type-algebra`: reduction of such expressions through the surjective quotient proves the forward direction. It needs neither finite generation of the maximal ideal nor a Noetherian assumption on the base. This is an elementary step.

Step 2 uses that same definition to form the subring C generated by chosen lifts. Because their residues generate the residue algebra, C maps onto k; hence k is the cyclic C-module generated by 1. For a local ring the intersection of all maximal ideals is precisely its sole maximal ideal, so the radical quotient in `lem-weil-pbc-artinian-finite-over-residue-finite` is exactly k. I read that node's statement: its first implication assumes an Artinian commutative target and module-finiteness of the radical quotient, and concludes module-finiteness of the target. Both hypotheses hold for C -> A. There is no assumption that C or R is Artinian, local, Noetherian, or a field. I also read the recorded Mathlib theorem, which permits restriction of scalars along this ring map. This is the substantive non-elementary algebra input, already represented in the DAG.

Step 3 writes the actual expression of an arbitrary element as a C-linear combination of module generators and substitutes polynomials for its C-coefficients. The union of the lifted algebra generators and the module generators is therefore an algebra generating set over R. This is elementary and does not silently invoke an unrecorded transitivity theorem.

Step 4 uses `def-weil-affine-spectrum` for the global-section identification and induced map, `lem-weil-pbc-lft-affine-pairs` for the necessity of finite type on the whole affine pair, and `lem-weil-pbc-lft-pointwise-criterion` for sufficiency using that same pair at each point. I checked both lemma statements: the first really quantifies over every affine pair, and the second really gives the converse from one pair at each point. There is no unsupported appeal to an affine criterion from a definition alone.

Step 5 uses `lem-weil-pbc-artinian-local-unique-prime`, which says exactly that Spec A is a singleton under the hypotheses here. `def-weil-affine-spectrum` states the corresponding singleton claim for the field k. Every inverse image in either source is empty or a singleton, and the finite-subcover argument is written out. This checks quasi-compactness without an unrecorded general theorem about affine morphisms. `def-weil-finite-type-morphism` then gives precisely locally finite type plus quasi-compact. The only non-elementary input in this step is cited explicitly.

I tested the zero-generator case (R -> k already surjective), the field case A = k, the nilpotent examples A = k[e]/(e^2) and Z/p^2, and the negative example Z -> Q[e]/(e^2): Q is not finite type as a Z-algebra, so neither is that Artinian ring. The same lifting proof works for a non-Noetherian base, for example k[x_1,x_2,...] mapping to k[e]/(e^2) with x_1 -> e and all other variables -> 0. The zero ring is excluded by the stated unique-maximal-ideal/local-field setting. In the scheme step I checked both possible inverse images (empty and singleton); no surjectivity to Spec R is used.

Against delivery-errors B--E: no new nodes, no relabelled clause, no proof hidden in a new statement, no unsourced non-elementary step, no use of a cited node's proof instead of its statement, and no added hypotheses. The proof dependency list is exactly the union of step uses. Every citation has a verbatim quote. Every step is under 2000 characters, and the entire proof text is under 3000 characters. The source, Mathlib searches and route provenance are recorded; no SGA source is used. The repository and launcher remain untouched, and no Lean or build tool was run.

## Unfinished work

None in the split. The required server dry run and direct push are the remaining delivery operations.
