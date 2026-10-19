# Stage-1 report: lem-coef-diagram-compact-pushout-descent

## Files written

- `dag/nodes/sec-six-functors/lem-coef-diagram-compact-pushout-descent.json`: seven proof steps; imported statement and hypotheses retained; no new node or Mathlib leaf.
- `citations.json`: relevant verbatim statements for all twelve step/node citations.
- This report. The earlier `searches.jsonl` is retained without alteration; its actual queries and results are now also retained in `mathlib_searches`, alongside the inherited searches. `repair.py` is a sandbox-only editing helper.

## Attachments

None. The preceding attempt's searches were retained, and I checked `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` again for the exact id, blueprint tag, and compact/pushout terminology. No project declaration states this item. The upstream master source is reference material, not a finished proof. No Lean file was written or compiled.

## WANTED

WANTED: Jacob Lurie, *Higher Topos Theory*, Lemma A.3.3.17, printed pp.883–884, https://people.math.harvard.edu/~lurie/papers/HTT.pdf. I read the statement, both compactness arguments, the two compatibility squares, and the final pushout online. This source is not archived in `literature/`; the proof remains agent-written following that source. Nothing was downloaded or added to the repository.

## Statement, source, and previous-attempt corrections

The current shared item is unsplit and has no Lean audit or blueprint update overriding its statement. Its statement agrees with the ordinary-category specialization of the indicated HTT argument. The extra fixed-cardinal diagram-presentation and finite-colimit hypotheses are explicit. I retained all clauses, including that the same specified maps P_d → Q_d are used and that the original maps a_d factor through F_0(d). No statement dispute was found.

The required initial dry run rejected the previous step 3 quotation: it was not a verbatim part of the canonical-density statement. More substantially, that density node states a canonical comma-category presentation, rather than the arbitrary-presentation factorization and eventual-equality facts used in the old proof. I removed that citation. The repaired argument derives those facts directly from presentability (defined in the item) and the existing filtered-set elementwise lemma. I also supplied the missing citation for replacing a filtered indexing category by a poset.

The old single paragraph about functor laws did not show how composition equations survive changing the stage. Steps 4–6 now first lift the Q_e-maps, then make their P_e-boundary equations hold, then construct prospective structure maps at every later stage and prove transition compatibility, and only then impose identity and composition on the Q_e-generators. Pushout uniqueness extends these equations from Q_e and F_t(e) to the entire pushout. No cancellation or monomorphism is needed.

The previous attempt also replaced the item's `created` field with self-creation by Q16. I restored the current repository's original Q01 metadata and its complete blueprint ancestry. The existing proof and report material, source, and search history were retained and repaired rather than discarded.

## Not duplicates

No new nodes were created. Whole-DAG statement/title searches and `tools/blueprint_refs.py search` found no blueprint node stating this simultaneous descent result. The pushout search found only the unrelated scheme example and sheaf-monomorphism lemma. Searches for presentable filtered presentations led to the existing `lem-coef-cardinal-filtered-poset-reindex`; the elementwise filtered-colimit result already exists as `lem-weil-pbc-filtered-colimit-sets-elementwise`. Both are reused, together with `lem-coef-ordinary-small-colimit-presentable` and `def-weil-pbc-category-colimit`.

## Review by Q16

I read `coord/delivery-errors.md` B–E in full and checked the actual statements, hypotheses, and sources of the four cited nodes. For the item I read HTT A.3.3.17 online; for the filtered-set lemma and colimit definition I read `literature/stacks-project/categories.tex`, Tag 04AX (`section-directed-colimits`, the explicit equivalence relation) and the colimit definition at Tag 002F. For the two existing Mathlib leaves I read `Mathlib/CategoryTheory/Presentable/Directed.lean:528–539` and `Presentable/Limits.lean:173–195`; the former preserves the cardinal, and the latter assumes exactly a diagram with fewer than that cardinal's morphisms. I also inspected `Presentable/Basic.lean:286–314`, confirming the Hom factorization/equality consequences independently. These are source reads, with no compiler invocation.

Step 1 cites the cardinal-filtered poset-reindexing node for a small κ-filtered poset preserving the given colimit. The category-colimit node supplies precisely the universal property used to prove pointwise computation; I wrote the functor maps and cocone correspondence out, instead of attributing a pointwise-colimit theorem to a definition.

Step 2 cites the filtered-set node for both clause (1), representation of an element, and clause (3), equality after one transition. The item's definition of κ-presentability transfers these clauses to Hom sets. κ is infinite regular, all Hom sets and presentations are small, and a κ-filtered poset is nonempty and filtered. Taking an upper bound of fewer than κ individual stages is exactly its assumed κ-filteredness. The short tail-cocone extension verifies that restricting to a tail preserves these colimits. This is a direct consequence of the cited statement and definitions, not an additional unsplit lemma.

Step 3 cites those same elementwise clauses for the original maps a_d; the identity-arrow injection bounds the number of choices. The colimit definition supplies transitions and the explicit cocone correspondence proving colim H_t(d) = G(d). Small-colimit presentability applies to the finite span P_d → Q_d and P_d → F_t(d); every object of that span is κ-presentable. The proof explicitly notes that H_t need not yet be a diagram on D.

Step 4 cites small-colimit presentability for the coproduct R_d indexed by arrows into d, and the filtered-set clauses for factorization and eventual equality. This is a discrete category with fewer than κ morphisms. Its summands Q_e and the boundary sources P_e are presentable by hypothesis. The displayed boundary equation is checked in G using naturality of f and the specified pushout squares, and the upper-bound argument makes it valid at all subsequent stages.

Step 5 uses only pushout uniqueness from the colimit definition. I checked both restrictions of transition compatibility, and both restrictions of the map to G. The Q_e restrictions are the previously fixed maps q_α, while the F_t(e) restrictions use naturality of the presentation transitions and f. This explains exactly how enlarging the stage preserves the prospective arrow maps.

Step 6 cites the filtered-set equality criterion on Q_e and pushout uniqueness. The identity and composition comparisons are fixed maps at stage r_1 with equal composites to G, not equations involving new uncontrolled choices. There are fewer than κ composable pairs because an infinite cardinal bounds the square of any smaller cardinal. Transition compatibility from Step 5 transports these equations to the actual maps at r_2. On F_{r_2}(e), the functor laws already follow from F_{r_2}; on Q_e they hold by construction. This is the full naturality/coherence argument required by HTT's second square.

Step 7 cites the colimit universal property for the displayed iterated pushout and the final gluing of the component maps into a natural map. It explicitly checks naturality by the two pushout legs, so no separate pointwise-functor-colimit theorem is silently taken from a definition node. Both presentability conclusions and the factorization of every original a_d are stated at the end of the construction.

I tested D empty, a one-object discrete D, arbitrary discrete D of size <κ, and a one-object category with nontrivial endomorphisms (where Step 6 enforces the multiplication relations). For D empty, the required nonempty filtered presentation still provides a stage and the conclusion is vacuous. For discrete D, only identities remain. Zero/initial P_d or Q_d and non-monic u_d use the same pushout universal property. Every equality is obtained by eventual equality, never by injectivity of a transition. The proof also works for a presentation with non-monic transitions. Each step is below 2000 characters, and no standard comparison or independent sublemma is concealed in a long step.

The only substantive non-elementary inputs are existing cited nodes, all Mathlib leaves. Each citation quote is copied from the current node's statement and includes the precise clause used. No new node merely restates the item, no source-dependent fact is cited only by its source, and no new-node hypothesis or duplicate remains to audit. No forbidden SGA source, live project write, git command in the shared repository, Lean edit, or compiler/build tool was used.

## Unfinished work

None in the split. Delivery is subject to the required server dry run and push; independent mathematical review remains the maintainer's task.
