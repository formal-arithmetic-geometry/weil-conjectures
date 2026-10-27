# Worker report: lem-sfb-space-valuative-separatedness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-valuative-separatedness.json: item, statement; split in three steps, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qc-valuative-existence-closed.json: one new statement-only prerequisite, unsplit; no Mathlib match. This is the general quasi-compact valuative-existence criterion (Stacks 03KA), not a restatement of separatedness or a clause of the item.
- citations.json: all three step citations, with literal excerpts of the cited statements.

## Attachments

None. Searched lean/WeilConjectures for the item tag and valuative separatedness, and read Compactification/ValuativeCriterion.lean. AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant is about schemes, not general algebraic spaces. No project declaration found states the item. No Lean was written or compiled.

## Wanted literature

None. Read literature/stacks-project/spaces-morphisms.tex: Tags 03KV (lemma-valuative-criterion-separatedness), 03KA (lemma-quasi-compact-existence-universally-closed), 03IX (definition-valuative-criterion), and 04Y0 (lemma-separated-diagonal-proper). Also read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability.proof.md and sk-thm-sf-ctf-stability-direct-images.proof.md.

## Corrections and route

The item's mathematical statement agrees with 03KV and is unchanged. Its statement dependencies now also expose fibre products, the point topology underlying quasi-compactness, and closed immersions. The imported item had no proof; it now carries the actual diagonal lifting argument. There is no statement dispute.

The existing lem-sfb-space-separated-diagonal-closed states exactly the final diagonal criterion of 04Y0; using it avoids creating new finiteness/monomorphism lemmas merely to reprove a result already in the DAG. The new 03KA prerequisite has independent content about arbitrary morphisms and arbitrary valuation diagrams. It does not assert separatedness and does not absorb the item's uniqueness-to-diagonal-existence argument.

The item's inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor reports None for this existing ancestry. I retained it and extended the existing via chain for the new node. The latest unit's direct-image proof no longer includes the alteration subargument spelled out in this item's inherited from.place. I record that provenance discrepancy without modifying the maintained ancestor chain or the unit. This split supplies the generic valuative step of the existing rigidified-Picard prerequisite and changes no unit-level route. No unit realization fields are touched because this is not the key node.

The fibre-product theorem is a generic tool from another unit, declared in split_report.tool_uses. Its categorical universal property, rather than anything hidden in its proof, is used here.

## Not duplicates

No existing DAG node was found with source Tag 03KA or 03IX. Whole-DAG searches for the tag, valuative existence and universal closedness found scheme criteria and special properness tests, but no general algebraic-space existence criterion. Whole-blueprint searches for 03KA, valuative, existence universally closed, universally closed, and valuative separated likewise found no equivalent imported node.

lem-sfb-space-qc-valuative-existence-closed vs lem-sfb-space-valuative-separatedness: the new node assumes existence for an arbitrary quasi-compact morphism and concludes universal closedness; the item assumes uniqueness for a morphism with quasi-compact diagonal and concludes a closed diagonal. The proof's first step is necessary to connect them.

lem-sfb-space-qc-valuative-existence-closed vs lem-sfb-space-separated-diagonal-closed: the existing node converts universal closedness of a diagonal into a closed immersion; it supplies no valuative-to-topological implication.

lem-sfb-space-qc-valuative-existence-closed vs lem-sfb-space-dense-open-valuative-proper: the latter concerns a normal noetherian space, a dense open and discrete valuation rings with generic point in that open; it is not the general 03KA result. The new node assumes neither noetherianity, normality, separatedness nor finite type, and quantifies over all valuation rings and all generic maps.

## Mathlib searches

All new searches used only the required msearch.py command, and their exact queries and returned summaries are in searches.jsonl and the nodes. I read every returned hit. Two semantic phrasings for the item find AlgebraicGeometry.IsSeparated.of_valuativeCriterion. The new-node searches, including the phrasing with field extension and dominating valuation ring, find AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion. Read Mathlib/AlgebraicGeometry/ValuativeCriterion.lean, especially its scheme variable at line 91 and declarations at 237 and 246: both results concern schemes. The Loogle query combining AlgebraicSpace and UniversallyClosed has no hits; the recorded source greps likewise find no algebraic-space infrastructure. Thus neither result is an exact match or a one-line specialization for the stated objects. No Mathlib leaf is claimed. The earlier search records on the copied item have been preserved, and the current logged searches appended.

## Review by NC

I read 03KV's statement and complete proof against the item: quasi-separatedness is precisely the assumed quasi-compactness of its diagonal, so no finite type, quasi-compactness of g itself, noetherianity or local-separatedness hypothesis has been inserted. I read 03KA and 03IX for the new node, including the field-extension convention: the new statement explicitly supplies K', a valuation ring A' with that fraction field and the local domination condition, and the two commuting equations. I corrected a draft source-tag transcription from 03K0 to the actual 03IX before delivery. I read 04Y0 and its proof for the existing final tool; its equivalence does not assume that g is of finite type.

In step 1, I opened lem-trf-space-fibre-products-etale-covers and checked its statement promises the sheaf fibre product is an algebraic space and an actual categorical fibre product. Those are exactly the properties used. For v into Y times_Z Y, the components a and b have the same Z-map; the commutative diagonal square makes both restrictions equal to u. The item's hypothesis gives a=b. The proposed lift is a itself, and both projection equations of Delta a=v are written out. This is an elementary use of the universal property and the assumed uniqueness, not an uncited valuative lemma.

In step 2, the cited new node concerns arbitrary quasi-compact algebraic-space morphisms, so it applies to Delta with no representability assumption required. Delta is quasi-compact by the item's hypothesis. Step 1 provides existence with the original ring R, which satisfies the new node's weaker existence requirement by taking K'=K and A'=R; identity domination holds. Thus universal closedness follows from exactly the cited statement, not a scheme-only analog. I checked the domains: the new target here is P=Y times_Z Y, an algebraic space by step 1.

In step 3, I opened lem-sfb-space-separated-diagonal-closed and checked its statement says, for any algebraic-space morphism, that it is separated if and only if its diagonal is universally closed, with closed immersion explicitly defined by scheme base changes. Step 2 supplies exactly that hypothesis for g. This gives every clause of the item's conclusion, including representability and scheme-test closed immersion; no extra descent or comparison is hidden.

I checked delivery-errors B1--B10: the new node has only a self-contained statement, source tags with their correct labels, actual recorded searches, no match falsely asserted, and populated blueprint provenance; the item retains imported metadata. Its basic spaces, valuation rings, fibre products and point topology each cite the existing defining statements. Quasi-compactness and domination are also defined inline. The raw strings render single TeX backslashes, not doubled TeX. I checked C1--C8 by opening each of the three cited statements; citations.json quotes are verbatim and cover every uses entry; proof_deps is their union. The existing diagonal theorem has no dependency path back to the previously unsplit item. The server checks are required to confirm cycles against the live graph. The only off-unit result used in the proof is declared as a generic fibre-product tool.

I checked D1--D5: the item itself proves the substantive passage from uniqueness to existence for the diagonal. The new node is the independently reusable topological existence criterion actually cited by 03KV. No new node repeats a clause of the item, and no source argument described as standard is being silently accepted in its proof. Each proof step is shorter than 2000 characters.

I checked E1--E7 on small cases. For R a field, j is the identity and the lifting calculation is literal. For empty Y the valuation squares are absent and the empty diagonal is closed. The identity morphism satisfies both hypotheses. A doubled-origin affine line over a field is a useful negative test: the two trait maps agreeing on the generic point violate the uniqueness hypothesis, so the argument does not incorrectly prove it separated. For the new node, the empty source has closed empty images and the identity has its tautological lift. The full statement permits arbitrary rank valuation rings and field extensions, and requires quasi-compactness rather than suppressing it. Nonreduced test schemes cause no issue because equality is equality of maps, not just equality of point images. I found no counterexample, missing hypothesis, wrong fibre product, or source error.

## Unfinished work

The item is fully split by one level. The sole new 03KA statement is intentionally unsplit for the next worker, as required. Its source proof reduces by base change to an affine target, takes an affine etale cover, and proves closedness of images by specialization and valuation domination; that argument is not placed in the new node's statement or proof. Delivery awaits the required server dry run and push.
