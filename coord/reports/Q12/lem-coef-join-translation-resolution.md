# Repair of lem-coef-join-translation-resolution

## Files written

- `dag/nodes/sec-six-functors/lem-coef-join-translation-resolution.json`: repaired stage-1 split; the statement, statement dependencies, Lean record and proof steps 1–8 are unchanged. Former steps 9–10 now use existing general comparison lemmas; step 11 proves the actual augmentation equality. No new nodes and no new Mathlib leaves.
- `citations.json`: 25 verbatim statement quotations, one for every step/node citation.
- `report.md`: this report. The preserved `searches.jsonl` was read and retained.

## Attachments

None. Searching the read-only `WeilConjectures/` source for the item's tag and join-translation names found no declaration stating both clauses. The existing stage-2 record is retained verbatim and is not evidence of a completed proof.

## Wanted sources

WANTED: Lurie, Higher Algebra, Notation 1.3.4.11, Lemmas 1.3.4.12–13, Remark 1.3.4.16 and Theorem 1.3.4.20, for lem-coef-join-translation-resolution; not archived locally. Read the online PDF at https://www.math.harvard.edu/~lurie/papers/HA.pdf, notably the translation and homotopy-colimit statements and the simplicial-model localization theorem.

WANTED: Lurie, Higher Topos Theory, Appendix A.2.9, Examples A.2.9.8 and A.2.9.29 and Corollary A.2.9.30, for lem-coef-join-translation-resolution; not archived locally. Read online at https://www.math.ias.edu/~lurie/papers/highertopoi.pdf. The older HTT.pdf URL failed; the alternate PDF supplied the Reedy and geometric-realization passages. PDF screenshots failed, so the online text extraction was used.

The proof remains marked agent-written: the explicit contractions and the Reedy/coend route expand the source rather than copying its cellular-induction proof. No SGA source is used; no Stacks tag states these enriched localization comparisons.

## Returned fault and repair

The human returned the 2749-character step 9 and 2203-character step 10 because they contained hidden non-elementary comparison arguments. I compared the preserved sandbox against the current repository's returned proof and continued the partial repair already in the sandbox. There was no preserved report. Steps 1–8, the item statement and the complete Lean record agree exactly with the current repository. The existing source ancestry and searches were retained.

For the first hidden argument I reuse `lem-coef-simplicial-model-nerve-localization`. Its statement identifies the entire infinity localization with the coherent nerve of bifibrant objects and explicitly specifies agreement with the ordinary inclusion. Its Kan specialization supplies exactly the comparison the former enriched-hammock zigzag was constructing. `lem-coef-simplicial-presheaf-projective-model` supplies Cartesian simplicial enrichment, and the Kan model theorem supplies functorial replacement and the cofibrant/fibrant classes. The comparison with all ordinary diagrams follows by applying the stated componentwise equivalence criterion to replacement. The general lemma is already present; making another node for this argument would duplicate it.

For the second hidden argument I reuse `lem-coef-bisimplicial-diagonal-space-colimit`. It states the coherent colimit of an arbitrary small bisimplicial set, specifies the coend cocone and includes naturality, without a Kan condition on its rows. This is precisely the general coend comparison formerly proved inside step 10. It has an independent current dependency closure and is not a restatement of either item clause: it concerns arbitrary bisimplicial sets, has no first-block projection or join-translation contraction, and does not identify the augmentation to X. That last identification stays in step 11 as the explicit equality of ordered-block maps.

I corrected two phrases in the preserved partial repair. The diagonal-colimit statement specifies its cocone, not an explicit formula for a transformation inverted in its proof; step 11 no longer relies on that internal proof. Step 10 likewise claims the specified cocone rather than attributing an extra derived-unit clause to its statement. The resulting longest non-elementary step is step 8 at 1615 characters. Every extracted non-elementary argument is a citation of an existing node rather than a newly duplicated node.

## Mathlib and duplicate searches

No node is created. I read the four preserved search-log records and their reported hits: the ordinal-sum grep had no hits; LeanSearch returned SSet, realization, ordinary colimits and simplicial splitting; Loogle returned subcomplex colimits; LeanFinder returned standard-simplex extra degeneracy, coskeletons and Dold–Kan. These are not the coherent join-translation resolution. The item retains those exact logged queries and its historical search records; no search was invented or rerun for an unchanged search question.

I inspected the actual Mathlib files `AlgebraicTopology/ExtraDegeneracy.lean`, `AlgebraicTopology/SimplexCategory/Augmented/Basic.lean` and `AlgebraicTopology/SimplicialSet/Subdivision.lean`. The preserved search verdict's shorter ExtraDegeneracy/Augmented filenames are not paths under SimplicialSet; the actual files give extra-degeneracy structures/contractions, the augmented simplex category, and subdivision/Ex, respectively. None alone states both clauses of this item. The already-cited extra-degeneracy lemma remains an existing Mathlib leaf.

Whole-DAG keyword searches and `tools/blueprint_refs.py search` were used before considering any extraction: no imported blueprint node matched bisimplicial colimits; the general localization search was broad, and the existing two comparison nodes give the needed statements. `blueprint_refs.py ancestor` confirms `prop-coef-integral-exceptional-adjoint`. The current main-20261015 ancestor proof, its chapter and its bound unit were read. The item's unchanged inherited ancestry serves the derived-adjunction paragraph; the foundational Reedy/coend route stays below that unit. No chapter or unit metadata is changed.

## Not duplicates

No new nodes. The two hidden comparisons are supplied by existing nodes, so there are no new/existing pairs requiring distinction.

## Review by Q12

I read the item against HA Notation 1.3.4.11 and Lemmas 1.3.4.12–13 online, and read the current statements of all fourteen distinct cited nodes. The target statement still defines the same ordered join, both restrictions, weak equivalences and coherent colimit, with no Kan or nonemptiness hypothesis added. There are no new nodes whose sources require separate review. The two reused general comparison statements were checked against HA 1.3.4.20 and HTT A.2.9.29–30, respectively, at the level needed here; their supporting proofs belong to their own nodes, not proof text borrowed by this item.

Step 1 uses the simplicial-set definition and computes composition of the two ordered-block restrictions; both augmentations and naturality are explicit. Step 2 uses the extra-degeneracy statement, not only its definition: every displayed equation matches a hypothesis there, including augmented degree -1 and n=0. The degeneracy s_n duplicates the final first-block vertex. Step 3 uses finite-limit preservation of realization for the product with Delta^1, and the definition of weak homotopy equivalence; the realized section and homotopy imply the claimed component and homotopy-group isomorphisms. These are direct consequences, with the basepoint-change path stated.

Step 4 uses the same contraction and realization statements in the reversed first direction. I checked that d_i^V=d_(n-i), s_i^V=s_(n-i) are obtained by ordinal reversal, that h_n=s_(n+1) has the displayed indices, and that reversing barycentric coordinates respects the quotient relation and augmentation. Step 5 uses exactly the exchanged-direction clause of the diagonal-equivalence statement, whose hypotheses need no Kan condition. Its last-block diagonal map is the one subsequently used.

Step 6 uses the Kan model theorem, Reedy theorem and unique nondegenerate decomposition. The decomposition identifies the latching equivalence relation, so the latching map is monic; at degree zero its source is empty. The Reedy category is the small Delta^op in a fixed universe. Step 7 is the written set-valued coend calculation and currying, using the function-complex definition, with its inverse and relation both given. Step 8 uses the Kan lifting classes, anodyne pushout product, relative Reedy matching characterization and derived Quillen adjunction. I checked that a boundary is monic, a horn is anodyne, that the product of two monos has the indicated union as source, and that degree zero uses the empty boundary. These establish both fibration cases needed for the derived-adjunction node, including its coherent unit/counit clause. No unsupported tensor-exactness or rectification result is hidden in this step.

Step 9 now uses the Cartesian simplicial-model assertion, the Kan cofibrant/fibrant classes, the full model-localization comparison and the componentwise criterion. All simplicial sets are cofibrant because the initial map is monic; Kan objects are precisely fibrant. The comparison agrees with the actual inclusion by its statement. Functorial fibrant replacement has weak-equivalence components, so its localization is a natural equivalence; this handles diagrams and transformations, not just objects. Step 10 uses the general diagonal-colimit statement with Z=B from step 1 and the cocone criterion from the functor/cone calculus. The diagonal statement explicitly supplies the coherent coend cocone and its naturality. Composing the apex with the equivalence a from step 5 preserves its mapping-space criterion. Step 11 uses the specified coend cocone; the equality of the last-block inclusion with (alpha star identity) followed by the diagonal last-block inclusion holds for every alpha, hence for the full coend and all its coherences. This is an elementary calculation, not a new lemma about arbitrary diagrams.

For C4 I checked each quotation in `citations.json` is literally part of the current cited statement, and removed the preserved partial repair's appeal to the inside of the diagonal lemma's proof. For C1 every non-elementary comparison in the repaired portion is now a named statement; remaining calculations are explicit ordinal identities and the mapping-space criterion. For B, no statement-only node is improperly supplied with a proof because none is created. For D, the item's contractions, diagonal weak equivalence, latching and matching arguments and augmentation equality remain here; the whole result is not moved to another node. For E, I tested X empty, X=Delta^0, X=Delta^1, n=m=0 and the degree-zero latching/matching cases. For Delta^1 the first-block fibers have explicit extra degeneracies, so no implicit connectedness or Kan hypothesis is used. For empty X all diagrams are empty and the colimit is empty; Delta^0 gives the constant point resolution.

I checked the full current statement/proof dependency closures of both reused comparisons for a path back to this item: neither has one. A general comparison whose proof is maintained in its own node can be cited in stage 1; this item does not claim that proof text as its own. The accepted generic `lem-cbc-enhanced-functor-cone-calculus` tool use is declared in split_report. No Lean file or compiler was touched, no live-project file was written and no git command was run in the shared repository.

## Unfinished work

No mathematical part of this stage-1 repair is left. Required full delivery dry run and push follow this report; their outcomes are recorded below.
