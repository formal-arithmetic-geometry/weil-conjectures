## Files written

- dag/nodes/sec-smooth-purity/def-kun-projective.json: definition-only split; no Mathlib match. No new nodes or Mathlib leaves.
- citations.json: empty list, because a definition has no proof steps.

## Attachments

None. The tag search for def-kun-projective and the concept/declaration-name searches across WeilConjectures found no project declaration defining this predicate. ProjectiveSpace.lean:130 defines only its ambient projective space; its properness instances do not define the existential embedding predicate. The exact master source remains reference material, not an attachment.

## WANTED

None. The blueprint, Stacks sources, and Lean sources needed for this definition are present.

## Corrections and observations

The original statement has the intended H-projective meaning and is not false or ill-typed. Stacks 01W8, morphisms-definition-projective, item (2), calls exactly this embedding condition H-projective; item (1) uses a broader projective-bundle convention. The statement now distinguishes those names explicitly, without changing the condition or adding a hypothesis. The imported dependency on the broad scheme-conventions bundle failed to identify projective space. I replaced it with the exact notion dependencies, including fields and the spectrum needed for the field structure morphism.

Whole-DAG concept searches and blueprint_refs.py searches for projective, H-projective and closed immersion found def-pc-projective-morphism, def-nagata-projective-space-base-change, def-nagata-relative-projective-space and def-weil-closed-immersion. I reuse the base-change projective-space interface because only the scheme and its projection are needed: there is no use of affine-chart morphism construction or a comparison theorem with relative Proj. The relative-Proj interface is therefore not a dependency. The existing def-pc-projective-morphism is recorded in same_as, rather than creating another predicate node. Its extra quasi-compact phrase is redundant for a closed immersion into finite-dimensional projective space: on an affine base open the latter has its finite standard affine cover, and a closed immersion is quasi-compact (01QT). The existing node's review likewise identifies these conventions.

## Unfinished work

None at this level. The definition has no theorem to prove. Its unsplit projective-space dependency remains an existing item for a later worker.

## Not duplicates

No new nodes were created. The item's same_as records def-pc-projective-morphism; the item retains its imported identity and states the original embedding convention explicitly.

## Review by NF

I read the item's master blueprint file in sk-prop-sf-kunneth-ordinary, its chapter and unit records, and Stacks morphisms.tex at definition-projective (Tag 01W8). The unit has no proof steps for this auxiliary definition, so there is no unit theorem route to replace. The imported condition matches item (2) of that Stacks definition, for arbitrary base schemes; I did not assume an affine or Noetherian base, finite type over a field, or properness.

I opened each dependency's statement. def-pc-scheme supplies schemes and their morphisms. def-weil-closed-immersion supplies the closed-embedding and structure-sheaf-surjection meaning, agreeing with its cited scheme definitions and the affine characterization 01QO. def-nagata-projective-space-base-change explicitly supplies the finite-coordinate polynomial Proj integral model, its base change, and the first projection to the base. I checked that against constructions.tex, definition-projective-space (Tag 01NF), and the project source ProjectiveSpace.lean:125–142. The classical dimension N requires coordinates 0 through N, not N coordinates; the item now says so. def-weil-field supplies an arbitrary nonzero commutative field; def-weil-affine-spectrum supplies Spec(k), including the one-point field case. The structure morphism is specified as part of the k-scheme, so the field clause is well-defined.

There are no proof-step citations: proof and proof_deps remain empty, and citations.json is empty. Consequently no theorem is taken from a definition, no hidden non-elementary inference carries a proof step, and no new node restates a clause. I checked that the statement dependencies name only notions actually used and do not point back to this item. I made no new node, so the statement-only-node and new-node duplicate checks have no instances here.

I tested the indexing at N=0 (one homogeneous coordinate, projective zero-space over Y), and the condition on the empty scheme (the empty closed subscheme is permitted). An arbitrary field, including positive characteristic and a finite field, still has the same Spec(k) structure-morphism formulation; nothing in the definition needs separable or algebraic closedness. A non-quasi-compact base is permitted: the statement does not require X or Y to be absolutely quasi-compact. The convention distinction is essential over general bases and is made explicit rather than silently replacing the fixed finite projective-space embedding by a projective-bundle embedding.

All seven Mathlib searches in the node were actually run using msearch.py and are logged in searches.jsonl. I read the returned signatures: Proj and its properness/separatedness declarations do not define this embedding predicate, and Loogle's projective hits concern modules. The second semantic phrasing and the morphism-directory grep also did not match. LeanSearch returned Internal Server Error, recorded as unavailable. No Mathlib leaf or project attachment was inferred from those related hits. This completes checks B–E for this definition, with no new source or statement dispute.

Preflight flagged the supplementary Stacks tag in the statement because the imported source record does not carry it. An attempted external-source addition was not carried by packaging: source is a maintainer-owned field. I restored the source record and removed the bibliographic tag from the mathematical statement, keeping the H-projective convention explicit. The exact Stacks tag and label supporting this terminology remain in this report; no dependency or mathematical condition changed.

## Second reading by NF

- Item statement: checked against Stacks `morphisms.tex`, Definition `definition-projective` (Tag 01W8), item (2); the arbitrary base, integer index, closed immersion into finite projective space, and factorization through the structural projection agree hypothesis by hypothesis.
- Proof steps: none are present because this is a definition-only node; `proof`, `proof_deps`, and `citations.json` are correctly empty.
- New nodes: none were created, so there are no new-node statements or node proof steps to audit; the existing `def-pc-projective-morphism` is recorded only in `same_as`.
- Definition dependencies: checked each cited dependency's statement and confirmed that schemes, closed immersions, projective space with projection, fields, and affine spectra are exactly the notions used.
- Edge cases: checked $N=0$, the empty scheme, arbitrary (including finite and positive-characteristic) fields, and non-quasi-compact bases; the definition remains well-typed and permits all intended cases.
- Searches and packaging: verified the recorded Mathlib searches and reran `deliver.py --no-push`; preflight passed.

Changes in this second reading: no mathematical or node-file changes were needed; this section records the source and edge-case audit required for delivery.
