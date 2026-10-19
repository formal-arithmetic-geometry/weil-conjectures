# Stage-1 report: lem-coef-model-weak-equivalence-nerve

## Files written

- `dag/nodes/sec-six-functors/lem-coef-model-weak-equivalence-nerve.json`: existing item proof audited and marked `split`; no new nodes.
- `citations.json`: verbatim interfaces for every non-elementary citation used by the proof steps.
- `report.md`: this worker report.

## Attachments

No attachment: the read-only slopmaster2 checkout at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` contains no declaration tagged `(blueprint: lem-coef-model-weak-equivalence-nerve)` and no declaration of the item’s theorem. The declaration in the shared `lean/` source is a `sorry` theorem and therefore is not an attachment.

## WANTED

- WANTED: Toën–Vezzosi, *Homotopical Algebraic Geometry II*, Appendix A, Proposition A.0.3, the paragraph before Corollary A.0.4, Corollary A.0.4 and Proposition A.0.6 (printed pp. 207–209), for the classifying-space and replacement arguments. The cited PDF is not archived locally; I read the relevant Appendix A text online at the node’s source URL during this audit. A local archival copy remains WANTED.

## What was wrong or changed

The repository item already contained the intended HAG II split, all seven proof steps, its blueprint ancestry, recorded Mathlib searches, and accepted tool-use declarations, but its status was still `unsplit` and there was no delivery report in this sandbox. I verified the item statement against the shared Lean declaration’s documented statement and against the existing DAG interfaces, then changed only the status, split-report date/summary, and delivery metadata. No statement clause was changed. The item has no Mathlib match: the searches find ordinary nerve/localization declarations, not the model-category weak-equivalence-nerve theorem.

## What could not be finished

Nothing remains for the stage-1 split. HAG II is available online and was read; its local archival copy is still WANTED. The generalized core/Quillen formulation remains correctly marked agent-origin.

## Review by Q82

I read the item node, its proof and source metadata, the unit/chapter records, the current main-20261015 blueprint ancestor proof, and every existing node named by its statement or proof dependencies. The item’s source is HAG II Appendix A, Proposition A.0.3, the comparison preceding Corollary A.0.4, Corollary A.0.4, and Proposition A.0.6. The local source checkout has no finished declaration for this item; the shared Lean theorem is still `sorry`, so it cannot close the node.

Step 1 uses `lem-coef-locally-constant-presheaf-slice` for the simplicial Quillen-equivalence and derived slice mapping-space comparison, and `lem-coef-kan-quillen-right-proper` for preservation of the contractible path-fibration total space under pullback. Their statements explicitly provide those two facts. Step 2 uses the same presheaf-slice node for evaluation and compatibility with representable maps, and `lem-coef-weak-equivalence-representable-local-model` for the fibrant replacement of a weak-equivalence representable and its equivalence-component value. Step 3 uses `lem-cbc-enhanced-functor-cone-calculus` for the Kan property of cores and `lem-cbc-simplicial-groupoid-localization` for extending the all-edges-inverting localization map with full mapping-space control. Step 7 uses `lem-coef-model-infinity-derived-adjunction`, whose statement supplies the derived functors, replacement formulas, and coherent unit/counit used for the Quillen clause. Steps 4–6 are elementary: functorial factorizations, two-out-of-three, closure of the object class, and the explicit nerve prism homotopies; they use no unstated node.

I checked hypotheses at each use: the category in Steps 1–2 is the small universe-enlarged weak-equivalence category; the path object is pulled back along the stated Kan fibration; the core in Step 3 is Kan and every component contains a represented vertex; and Step 7 applies the model-category factorization hypotheses and represented-class closure already present in the item. The `citations.json` quotes are verbatim portions of the cited node statements. I found no duplicate node, no cycle, no additional definition node, and no hidden non-elementary lemma in the replacement/prism steps. The existing tool-use declarations for the two generic enhanced-category facts are retained.

I also opened HAG II online and read Proposition A.0.3, the four-term comparison on printed p. 208, Corollary A.0.4, Proposition A.0.6 and the following functoriality discussion. The source agrees with the presheaf route. Its last discussion assumes simplicial left Quillen functors and fibrant objects; Step 7 extends that discussion using the explicitly cited general coherent derived-adjunction statement, rather than silently applying the restricted discussion to an arbitrary model category. I tested the statement on the empty object class, a terminal model category, and the discrete model structure on sets (where the nerve and core are both the groupoid of isomorphisms). No fibrancy of the raw nerve or properness of the arbitrary model category is used.

I checked the two proof steps longer than 2000 characters. Step 1 is one explicit path-fibration computation in the cited simplicial slice model structure: endpoint fibration, contraction, pullback, and fiber evaluation of a cofibrant vertex into that fibrant model. These are the model axioms and a direct mapping-object calculation, not a hidden input. Step 7 applies the cited coherent adjunction and restricts its already-given functors and unit/counit to replete full subcategories; its later paragraphs identify the actual LQ/L maps and use two-out-of-three. Both are expanded routine arguments, so I retained them without inventing restatement nodes.
