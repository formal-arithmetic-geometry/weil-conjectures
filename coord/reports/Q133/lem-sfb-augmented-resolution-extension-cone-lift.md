# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-augmented-resolution-extension-cone-lift.json`: statement, split into five proof steps; no whole-item Mathlib match. Retains all pre-existing searches, provenance and blueprint fields. Adds the existing definition of short exactness to the statement and its dependencies, without changing any mathematical hypothesis or conclusion.
- `citations.json`: eleven step/node entries, each checked as a literal substring of the cited statement.
- `report.md`: this report. No new DAG nodes or Mathlib leaves.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, augmented resolutions, augmentation lifts and extension/cone combinations found no declaration giving every clause. Related resolution and cone declarations concern different constructions. No Lean file was written or compiler invoked.

## WANTED

None needed to complete this split. The original provenance requests a direct reference for the extracted internal-category argument; the proof here instead explicitly assembles existing general abelian-category facts. Its `proof_origin.by` is `agent`, not a claim that the latest blueprint contains this argument verbatim.

## Corrections and searches

The original mathematical statement is correct. Its proof was empty and its statement used short exactness without naming the already existing definition. I added that citation and supplied the proof, keeping the cone convention and every conclusion. No statement dispute or route change was necessary.

Read the chapter and unit records. The latest blueprint's direct-image proof, paragraph (3), is the ambient route; the algebraic extension diagram is exposed in the parent `lem-sfb-internal-bar-roof-adjunction`, now proof step 5. `blueprint_refs.py ancestor` reports a null nearest imported ancestor. I retained that existing null value and the full via chain, and made the explanation explicit in `split_report.blueprint` rather than inventing an ancestor. Whole-blueprint searches for cone, augmentation and kernel found no imported node stating this complete lift construction; `same_as` stays empty.

Whole-DAG concept and title searches located three exact tools already present: `lem-weil-pbc-abelian-short-exact-kernel`, `lem-weil-pbc-cochain-complexes-degreewise-exact`, and `lem-pc-cone-short-exact-quasi-iso`. They replace any need for new auxiliary nodes. The remaining arguments are component equations and inverse cancellation written in the item itself.

Ran the required search command for the item with LeanFinder (two distinct phrasings), Loogle, grep and LeanSearch. Read the output and the relevant Mathlib source: `mappingCone.lift` and component lemmas at MappingCone.lean:501-525, `descShortComplex` at ShortExact.lean:53 and its quasi-isomorphism at :137, `ShortExact.fIsKernel` at ShortComplex/ShortExact.lean:162, and degreewise short exactness at HomologicalComplexAbelian.lean:70. The first constructor requires the cocycle and compatibility as inputs; it does not construct the unique kernel factorization from the augmentation. The whole item is therefore an assembly proof, not a one-line specialization. The quasi-isomorphism portion and kernel tool already have Mathlib leaves. All current command records were copied from `searches.jsonl`; inherited Q88 searches were preserved, including the unavailable LeanSearch result.

## Not duplicates

No new nodes. The existing generic kernel, degreewise exactness and cone quasi-isomorphism nodes are cited directly.

## Unfinished work

None in this stage-1 split.

## Review by Q133

I read the latest blueprint direct-image paragraph (3) and the parent's extension clause to fix what this node serves. For the actual algebra I read Stacks `homology.tex`: Tag 0106 (`definition-kernel`), Tag 010E (`definition-exact`), the abelian definition 0109, and Tag 0114 (`lemma-cat-cochain-abelian`); and `derived.tex`: Tag 014E (`definition-cone`), the construction preceding Tag 0152 (`lemma-derived-canonical-delta-functor`), and Tag 05RU (`definition-unbounded-derived-category`). The source's cone has off-diagonal +i and its distinguished triangle has negative projection. Those are precisely the item's conventions.

For step 1 I opened the kernel lemma's statement: it asserts the unique factorization of every map killed by the second arrow. Here that map is ell composed with partial_1, killed because p ell = e^0 and e is a chain map. Its source is P_1, which needs no projectivity. The exact-sequence definition supplies monicity of i. The derived-category definition supplies the chain equation; nothing about injective or projective resolutions is imported.

Step 2 uses only that monicity and the complex identity partial_1 partial_2 = 0. I checked the sole potentially nonzero equation for bar f in degree -2; in degree -1 both sides land in a zero term. The cited derived-category definition explicitly gives cochain maps, shifts and differential identities. This is an elementary calculation, not an unmentioned lifting lemma.

Step 3 substitutes single objects into the cited cone matrix, then checks the two nontrivial equations of kappa separately. For v the equation is p i = 0. The cone projection is the identity on N in degree -1; its negative is the distinguished arrow, so no extra sign belongs in kappa^{-1}. No comparison is hidden behind an identification of complexes: the terms and all differentials are displayed.

Step 4 cites the degreewise-exactness lemma exactly for passage from the given degree-zero sequence and zero sequences to a short exact complex sequence. The cone quasi-isomorphism lemma's statement specifies the restrictions to BOTH cone summands; these identify its canonical map with v. Its hypotheses allow arbitrary abelian categories and complexes and impose no splitting. The cohomology assertions follow from its quasi-isomorphism conclusion and the displayed definition of H^r on the single complex X[0], rather than from an uncited long exact sequence or a cokernel comparison. Both cited theorem nodes are existing Mathlib leaves.

Step 5 checks both component equalities and then uses only functoriality of Q and inverse cancellation. The localization definition explicitly inverts quasi-isomorphisms. The assumption that e is a quasi-isomorphism is retained, although this particular cancellation only requires the already proved quasi-isomorphism of v. No stronger boundedness, projectivity or existence of an arbitrary lift was assumed.

I tested zero objects and the split extension with P = X[0], including nonprojective X. Then f = 0 and kappa is just the supplied section. For a nonsplit sign test in abelian groups, use 0 -> Z --2--> Z -> Z/2 -> 0, P = [Z --2--> Z] in degrees -1,0, and ell = id. Then f = id and kappa is the identity of this two-term cone; both chain equations and the positive projection formula hold. This also checks the distinction between the projection and the negative triangle arrow. For an acyclic two-term P resolving zero the same equations still apply, and no boundedness of the negative tail was used.

I checked delivery-errors B--E against the written files. There are no new statement-only nodes to duplicate or misclassify, every cited fact is in the cited statement, the argument does not depend on its parent, and no clause has been moved into a renamed node. All steps are under 750 characters, so none hides a long auxiliary proof. The five steps and the verbatim citation file cover every proof dependency. No SGA source, build tool or repository write was used.
