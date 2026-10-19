# Stage-1 delivery: lem-coef-simplicial-invertible-arrow-pushout

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-invertible-arrow-pushout.json`: statement, split into nine steps, statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-groupoidal-cofibrant-nerve-detection.json`: statement-only, unsplit; Dwyer–Kan Corollary 9.6, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-cofibrant-localization-diagonal-nerve.json`: statement-only, unsplit; Dwyer–Kan Proposition 10.2, no Mathlib match.
- `citations.json`: one verbatim statement quotation for each citation in each proof step.

## Attachments

None. Searches of `WeilConjectures/` in the read-only slopmaster2 checkout for the item tag, Bergner, Dwyer–Kan, simplicial categories and coherent inverses found no declaration stating the item or either new lemma. Ordinary invertible morphisms and simplicial objects do not supply these enriched assertions. No source declaration with sorry was treated as a proof.

## Literature wanted

WANTED: J. Lurie, *Higher Topos Theory*, Definition A.3.2.12, Remarks A.3.2.13–15 and Example A.3.2.18, printed pp.862–863, archival copy in literature/, for the item. Read the public Harvard PDF online.

WANTED: W. G. Dwyer and D. M. Kan, *Simplicial localizations of categories*, Sections 7–10, especially Corollary 9.6 (p.280) and Proposition 10.2 (p.281), archival copy in literature/, for both new nodes and the proof. Read the public Rochester PDF online, including the statements and proofs in Sections 9 and 10.

WANTED: J. E. Bergner, *A model category structure on the category of simplicial categories*, Lemma 2.4 and Section 4, archival copy in literature/, for the existing countable-witness input. Its exact required statement is already a DAG node, read in full; no proof claim from its implementation is used.

No Stacks tag states these simplicial-category theorems. The source fields give theorem numbers in the actual publications rather than invented Stacks tags. No SGA source is used.

## What was wrong or needed work

The item was a statement-only child, not an incorrect statement. HTT Remark A.3.2.14 confirms the arbitrary factorization and arbitrary functor formulation. Its source's invertibility hypothesis is a theorem for simplicial sets, not an elementary property of a pushout, so merely quoting that remark would move the whole item into another node.

Several apparently useful generic nodes cannot be cited here: `lem-coef-scat-bergner-left-proper-pushouts` and `lem-coef-fixed-object-simplicial-free-calculus` depend on `lem-coef-coherent-nerve-comparison`, which reaches this item through the localization and walking-groupoid chain. The general derived-adjunction node also reaches this item through cosimplicial frames and hammock comparison. I checked those dependency paths and instead used the independent fixed-object properness theorem and Brown split-factorization statement.

The proof therefore reduces to two cofibrant intervals on the fixed labelled object set, compares their pushout with strict partial inversion at the level of the diagonal classifying nerve, and only then applies the groupoidal nerve criterion. The original factorization can have additional objects: step 2 compares it in the undercategory and does not assume it has just two objects.

The existing chapter/unit binding and every maintainer-owned field are retained. The current blueprint ancestor's proof paragraph 2 is the coefficient-adjunction computation at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`; the supplied historical unit binding is not rewritten. These technical lemmas serve its existing coherent-realization ancestry and do not replace the coefficient proof route.

## Searches and Not duplicates

The item and both new nodes were searched with the required msearch command, using LeanFinder, LeanSearch, Loogle and Mathlib grep. A second natural-language phrasing was run for each. The item retains its inherited searches and adds the current logged searches. New nodes record only commands actually run during this attempt, with the exact query and raw summary in searches.jsonl. The first localization Loogle pattern named an unknown identifier; its diagnostic is retained and a corrected identifier was also searched. No online service outage was represented as a negative theorem result. Hits about ordinary nerves, localization of abstract model categories and ordinary pushout isomorphisms do not have the displayed enriched statements; hence zero Mathlib leaves.

I searched the whole DAG by groupoid-completion, diagonal-nerve, partial-inversion, theorem-number and statement keywords, and used blueprint_refs.py searches for invertibility, groupoid completion, nerve pushout, diagonal nerve, cofibrant localization, groupoidal and partial inversion. No blueprint node states either new result. All new blueprint records point through this item to the supplied ancestor, with exact places and the complete via chain.

## Not duplicates

- lem-coef-groupoidal-cofibrant-nerve-detection vs lem-coef-cofibrant-homotopy-groupoid-completion: the existing result compares one cofibrant category with its degreewise groupoid completion. The new result detects mappingwise equivalences of an arbitrary map between two cofibrant homotopy groupoids by its diagonal nerve; the existing statement has no such detection clause.
- lem-coef-groupoidal-cofibrant-nerve-detection vs lem-coef-cofibrant-completion-nerve-equivalence: the existing result asserts nerve invariance under total completion for one cofibrant category, even without groupoidal pi_0. It does not detect mappingwise equivalences from a nerve comparison.
- lem-coef-cofibrant-localization-diagonal-nerve vs lem-coef-cofibrant-completion-nerve-equivalence: the new result concerns partial inversion along an arbitrary cofibration of cofibrant fixed-object categories; the existing result treats total inversion only.
- lem-coef-cofibrant-localization-diagonal-nerve vs lem-coef-cofibrant-simplicial-inversion: the existing statement gives a Bergner homotopy-pushout comparison and a derived coherent-nerve assertion for total completion of the subcategory. It does not assert invariance of the *diagonal classifying nerve of the partially localized target*. Identifying these nerves would require an additional comparison theorem, and the existing node also depends transitively on this item. The new statement is exactly the independent diagonal-nerve theorem in DK 10.2.
- lem-coef-cofibrant-localization-diagonal-nerve vs lem-coef-simplicial-invertible-arrow-pushout: diagonal-nerve invariance needs no invertibility of the localized arrows and asserts no mappingwise equivalence or Bergner cofibration. For the walking arrow itself it preserves the classifying-space homotopy type while changing the path-component category to a groupoid. Thus it is not the item's conclusion in new words.

## Review by N9

I read HTT Definition A.3.2.12 and Remark A.3.2.14 in the online text, checking especially that the latter uses a cofibration A to E followed by a weak equivalence to the walking isomorphism, rather than requiring the map from A to C to be a cofibration. Example A.3.2.18 identifies the simplicial-set case. I read DK 9.6 on printed p.280 and DK 10.2 on p.281 with their proofs and the preceding conventions: both use one fixed object set; a strong cofibration means a cofibration between cofibrant objects; the nerve is the diagonal of the bisimplicial ordinary nerve, not the coherent nerve. These precise hypotheses and constructions are written into both new statements. The item proof is marked agent-written because it assembles these ingredients and the sources are not archived locally.

For step 1 I read the full statement of the sorted-algebra model theorem: it gives the free evaluation adjunction, boundary generators and the needed two factorizations. I read the interval-lifting statement for its exact I generators. A map against a U-boundary cell is a mapping-set boundary square; no assertion from the proof of either node is needed. The labelled-target argument verifies the transfer from fixed-object cofibrations and trivial fibrations to the Bergner classes. The Bergner model structure and its generators are the structure already specified in the item's context, not a use of the cyclic coherent-nerve theorem.

For step 2 I opened the Brown split-factorization node: its statement gives both a trivial-fibration factor and a *cofibration* section, which is essential for the argument after cobase change. The lifting-class-closure node states pushout closure, and the cell-stability node states two-out-of-three. Under-category factorizations and lifting properties are inherited by factoring an underlying arrow and composing its structure map from A; limits/colimits use the usual compatible structure maps. Thus all Brown hypotheses hold in A/sCat. I verified that the proof needs neither left properness nor cofibrancy of C and that it handles E with additional objects.

For step 3 I read the countable-equivalence-witness node, including its warning that A to H need not be a cofibration. I did not assume it was: the sorted-model factorization replaces it by A to K to H. K retains contractible mapping sets and maps to C with exactly the prescribed vertex. D uses two distinct *labels*, even if their images in C coincide, so the witness's two-object hypothesis really holds.

For step 4 I checked the component pushout directly using the adjunction to discrete enrichment. The pushout of the two copies of the walking groupoid over their common arrow is the same walking groupoid, because inverse arrows are unique. Cofibrancy of P follows from cofibrancy of K and cobase change of j_0; no cofibrancy of the strict localization L is claimed.

Step 5 uses exactly the new partial-inversion nerve theorem: its V is A, its B is K, and both are cofibrant on the same object set. Groupoid completion of A is J, so its displayed target is exactly L. Step 6 uses the existing fixed-object left-properness statement with u=q_0 and i:E_0 to P. The latter is the pushout of A to K, so its cofibration hypothesis is checked on the correct leg. I read the realization-finite-limits statement for its preservation of coproducts and finite products, and the bisimplicial-diagonal statement for rowwise weak equivalences. The finite-product/disjoint-union homotopy-group argument is supplied explicitly, rather than attributed to either node beyond its statement.

In step 7 I verified both cofibrancy hypotheses and both groupoidal pi_0 hypotheses before applying the new nerve-detection statement; applying it to L would have been invalid because L was not shown cofibrant. Step 8 writes the labelled lifting square against an arbitrary Bergner fibration and uses precisely the mappingwise Kan condition from interval-lifting, the fixed-object model lifting axiom from the sorted theorem, and pushout closure from the lifting-class node. This is an elementary unwinding of a lifting property and a pushout universal property. It proves the comparison in arbitrary C without assuming distinct endpoints. Step 9 uses the already cited two-out-of-three and cofibration pushout closure to recover the arbitrary original E and both requested conclusions.

I checked delivery-errors B1–B10: new nodes have statements only, all objects and hypotheses are introduced, the displayed nerve is defined inline, TeX is escaped once in JSON, source numbers are exact and no Stacks tag is invented, every recorded query ran, and neither attachments nor leaves were invented. For C1–C8 I opened every cited statement, checked its precise clause against the step, included every non-elementary ingredient as a node citation, and avoided the known cycle-producing nodes. The citations file quotes the statements verbatim. No off-route replacement is made; Brown is declared as a generic tool even though its current unit binding is the item's own unit.

For D1–D5 neither new node restates the item: one is a detection criterion with groupoidal hypotheses, the other a statement about a single diagonal nerve with *no* invertibility assumption. The item's steps carry the intervening argument, cofibrant comparisons and arbitrary-object transfer. For E1–E7 I checked the object sets, exact selected vertices, the legs on which properness applies, all cofibrancy hypotheses, and the distinction between diagonal and coherent nerves.

Small cases: if C has one object and f(a) is the identity or a nontrivial homotopy unit, the two-label construction still applies; if C is non-Kan none of the fixed-object inputs assumes Kan; if E has additional objects the undercategory comparison still applies; an empty C admits no functor A to C, so the item is vacuous there. For the new lemmas O may be empty, in which case all nerves are empty and the unique comparisons are equivalences. For discrete cofibrant groupoidal categories on one label the nerve criterion reduces to the identity-only case. The partial-inversion nerve theorem applied to A itself gives the interval nerve and the nerve of the walking isomorphism, both contractible, while pi_0 changes: this tests why it cannot be mistaken for a mappingwise-equivalence theorem. The detection theorem explicitly retains its cofibrancy and groupoidal hypotheses.

Every proof step is below 2000 characters. I checked the inline constructions for hidden non-elementary subclaims: the two actual nerve theorems are separate nodes, the existence of a witness is a cited node, properness and the diagonal theorem are cited, and the remaining labelled lifts and component pushout calculations are written out. No statement dispute was found. Nothing remains unfinished in the one-level split; the two new nodes are intentionally unsplit and are future stage-1 items.
