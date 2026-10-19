# Worker report: det-lem-coefficient-finite-descent-hom

## Files written

- `dag/nodes/sec-six-functors-basics/det-lem-coefficient-finite-descent-hom.json`: repaired split, ten proof steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-representative.json`: statement, Mathlib leaf for bounded representatives.
- `citations.json`: verbatim substantial statement quotations for every use by an item proof step.

## Attachments

None. Searches under WeilConjectures/ for the exact blueprint tag, finite-descent notions and the constructible cocone Hom names found no declaration stating the entire three-clause item. The item's slopmaster2 audit is none. Upstream master sorry declarations were not treated as proofs.

## WANTED

None.

## What was wrong and repaired

The human return names the original three proof steps (3882, 2233 and 2004 characters) as hiding lemmas. The original statement and proof route have been preserved. The first argument now cites the existing localized-adjunction Mathlib leaf lem-sfb-adjunction-localization, the second uses existing generic ring/module-colimit and tensor-colimit nodes, and the third cites a bounded-representative Mathlib leaf. The comparison with T_{E,F}, T_{E,Qlb}, the unit-compatible transitivity comparison, and the explicit transition identity are retained. No Lean, build tool, or live project file was changed. A first server-check attempt rejected the sandbox's root-level node layout before checking anything; the files now have the required dag/nodes/chapter layout. Logged searches and original item search records are retained.

## Not duplicates

lem-sfb-bounded-representative vs def-weil-pbc-bounded-derived-subcategories: the existing definition describes finite cohomological support, whereas the new Mathlib leaf produces a complex with finite termwise support and an isomorphism to the derived object.
lem-sfb-bounded-representative vs lem-trf-filtered-bounded-localization-comparison: the existing statement concerns filtered derived categories and their embeddings, not the ordinary derived category of an arbitrary abelian category.

## Review by Q33

I read the current blueprint statement, its three numbered proof paragraphs, the chapter record, and the unit sk-thm-sfb-qlbar-two-colimit (particularly its clause (2)). The statement is unchanged. I also read the statements of all cited DAG nodes. The small-site universe is chosen to contain both the coefficient diagram and a site skeleton.

Step 1 uses the closed sheaf tensor and the ordinary scalar adjunction; finite-limit preservation in the two flatness statements, together with right exactness, gives exact scalar extension. Step 2 uses the termwise adjunction statement, exact-functor localization, and the existing lem-sfb-adjunction-localization Mathlib leaf. I read Mathlib/CategoryTheory/Localization/Adjunction.lean, especially localization at lines 81–115 and its unit/counit formulas at 118–130: the factorization-isomorphism hypotheses are supplied by exact-functor localization. Step 3 binds the adjoints to the exact left-derived coefficient functors by their definitions. Steps 4–5 retain the tensor multiplication map and inverse, the composite-unit equation, uniqueness of the comparison, and alpha_{B'}(f_{B'}) = t alpha_B(f); thus clause (3) still concerns the specified extension map, not an arbitrary bijection.

Step 6 applies finite composita and the coefficient ring colimit, explicitly extending a cocone through EH to justify restricting to fields containing E. Step 7 applies the site-level lem-sfb-directed-ring-sheaf-module-colimit; I rejected the superficially similar topological-space-only sheaf-algebra node because its domain does not cover the pro-etale site. The ring maps and scalar-action triangles are the inclusion-induced maps. The internal-module/sectionwise-module equivalence applies because the small-site abelian sheafification is strong monoidal. Step 8 uses the independent-coefficient tensor-colimit theorem and the balancing coequalizer to identify tensors, then checks the differential and lower bound degreewise. These are exactly the statements used, not constructions taken only from another node's proof. I read Stacks sites-modules.tex Tag 03DB (lemma-limits-colimits) and Tag 03EP (lemma-tensor-commute-colimits), plus sites.tex section 00YR on algebraic-structure sheafification, as the underlying source for these existing generic tools.

Step 9 checks that Spec k is Noetherian and applies finite-type preservation; bounded constructibility supplies an interval [a,b]. I read DerivedCategory/TStructure.lean lines 90–122 and 180–186 for the new representative leaf: its statement applies to any abelian module category, including internal coefficient modules, and requires no projective or flat representative. Step 10 applies the exact constructible Ext-continuity statement with Lambda = E, q = r, Noetherian X, bounded constructible C and the common lower bound a. The earlier transition identity identifies its canonical cocone legs with extension of scalars.

I checked C = 0, D = 0, F = E, shifts with negative r, single-degree complexes, and arbitrary finite cohomological interval. The representative leaf requires no extra coefficient hypothesis; the existing localized-adjunction leaf requires only the supplied localization factorizations and also handles identity localization. A proposed new site-colimit node became unnecessary when the synchronized DAG supplied lem-sfb-directed-ring-sheaf-module-colimit; it is reused, not recreated. The sole new node has a statement-only body, the exact Mathlib declaration, source lines and actually executed searches. The blueprint and DAG searches found no equivalent existing ordinary bounded-representative node. On resumption, a current-DAG search found lem-sfb-adjunction-localization with exactly the required localized unit/counit formulas; I read its complete statement and the cited Mathlib declarations, replaced the retained duplicate lem-sfb-adjunction-localizes with this existing leaf, copied the actual formulas into the step-2 citation, and dropped the never-committed duplicate. The search log is retained unchanged; the bounded-representative grep query now uses the exact logged pattern, with its source directory recorded by the log. All ten steps are below 2000 characters. No SGA source is used. The mathematical route is unchanged; generic off-unit tools are declared in split_report.tool_uses. Nothing remains unfinished except the independent maintainer review after delivery.
