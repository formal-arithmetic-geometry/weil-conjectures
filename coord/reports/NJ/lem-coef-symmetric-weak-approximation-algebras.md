## Files written

Repair of `lem-coef-symmetric-weak-approximation-algebras`, group NJ, stage 1 only.

- `dag/nodes/sec-six-functors/lem-coef-symmetric-weak-approximation-algebras.json`: returned item, now twelve steps. Statement and Lean record unchanged. Old Steps 1–4 and 6–9 retained verbatim; old Step 11 retained as Step 12 with numerical references updated. Only returned Steps 5 and 10 substantively rewritten.
- `lem-coef-symmetric-cartesian-cylinder-slice-comparison`: new statement-only lemma, unsplit, no Mathlib match. Supplies the cylinder/slice/comma equivalences hidden in old Step 5.
- `lem-coef-symmetric-cartesian-cylinder-edge-comparison`: retained extraction, corrected statement and searches, unsplit, no Mathlib match. Supplies coherent Cartesian-lift comparison hidden in old Step 10.
- `lem-coef-symmetric-relative-product-comparison`: retained extraction, corrected statement and searches, unsplit, no Mathlib match. Supplies relative-cone comparison hidden in old Step 10.
- `lem-coef-symmetric-inert-projection-detection`: retained extraction, corrected statement and searches, unsplit, no Mathlib match. Supplies the all-inert test hidden in old Step 10.
- `citations.json`: 47 step/node entries, quoting the full verbatim statement of every cited node so its hypotheses remain visible.
- `searches.jsonl`: original log retained, plus actual searches through the required msearch command. Each new node records real queries and actual result records. Unlogged provisional queries of the interrupted extraction were replaced.
- `prior-attempt/interrupted-item.json` and `prior-attempt/retained-Q67-report.md`: preserve the interrupted proof and historical report from the returned repository head. Sandbox references only.

Four new nodes, zero Mathlib leaves. Each new node has empty proof/proof_deps, null proof_origin, complete objects and hypotheses, and full inherited blueprint ancestry. No Lean, compiler or Lake tool was used.

## Attachments

None. Searching the read-only slopmaster2 project under WeilConjectures/ for the item id, weak approximation, Cartesian cylinder, relative limits and inert projections found no declaration stating the item or the extracted lemmas. Upstream master was searched as reference only; its ordinary module-object tensor products are unrelated and its sorry declarations are not proof evidence.

## WANTED

WANTED: Jacob Lurie, Higher Algebra (18 September 2017), Definitions 2.1.1.10, 2.3.3.6, 2.3.3.20, Remark 2.1.2.9, and Theorem 2.3.3.23(1), printed pp. 266–268, for the item and all four new nodes. I opened and read the official PDF online at https://people.math.harvard.edu/~lurie/papers/HA.pdf during this repair. It is not archived in literature; no download or literature edit was made. The proof remains agent-origin. The new lemmas are agent expansions of the indicated source arguments, not separately numbered source theorems. No Stacks tag states these quasicategorical results; no unrelated tag is assigned. No SGA source is used.

## Return repaired

The human returned old Step 5 (2317 characters) and old Step 10 (2450 characters) for hidden non-elementary arguments. This repair changes the dependency graph rather than merely inserting paragraph breaks. Old Step 5 now cites cylinder-slice comparison for K_x → K'_x and the comma-to-F_g equivalence; the remaining argument applies weak contractibility and existing coinitiality and cone-restriction theorems. Old Step 10 becomes Steps 10–11: relative-product comparison inverts the canonical Cartesian edge, Cartesian-edge comparison covers every Cartesian edge, and inert-projection detection concludes preservation of all inert arrows. These new nodes do not state an algebra-restriction equivalence or a clause of the item itself. The item still constructs the right Kan extension and identifies the full coherent restriction functor.

The interrupted attempt duplicated its comma and Cartesian-edge steps, dropped the forward implication and closing equivalence, and left stale numbering. I restored unaffected steps from the current returned repository proof before inserting these extractions. The original route, statement, Lean record, source, historical searches and maintainer-owned metadata are preserved. Step 5 has 1043 characters, Steps 10–11 have 956 and 835, and the longest remaining step is Step 1 with 1741. No non-elementary step exceeds 2000 characters.

## Sources and edge cases for the new nodes

For cylinder-slice comparison I read HA 2.3.3.23(1)'s cylinder and coinitiality argument, printed pp. 266–267, and the actual existing Cartesian mapping-fibre, localization, join-coslice, join-cone, opposite-slice and one-sided-fibration statements. The retraction must invert Cartesian edges, not merely agree on endpoints: this is explicit. K_x and K'_x are left fibrations over D; their fibre map becomes postcomposition by an equivalence under the Cartesian mapping-space formula. Fibre detection makes the map an equivalence over D, identifying the full inert subcategories. The iterated slice comparison retains all coherent triangles; it is an equivalence rather than a false literal identification of a comma in E with a pullback in P. Over β:d'→d both models encode γ:x→g(d') and a triangle g(β)γ≃α, with the face restrictions given by ordered joins. This is the non-elementary comparison extracted as a node. No weak-contractibility or unary-equivalence hypothesis is built into the lemma; the parent applies these afterward.

For Cartesian-edge comparison I read the converse (ii) on p. 268, Cartesian mapping-fibre and the dual cocartesian composition/initiality interfaces. The specified factorization space is contractible by the mapping-fibre universal property. Comparing two Cartesian lifts makes the intervening edge Cartesian over the identity, hence an equivalence, also for degenerate base edges. The statement retains the triangle and its higher data, not merely isomorphism classes of domains.

For relative-product comparison I read the product use on HA p. 268 and the relative universal-square definition. That square for the target cone makes the fibre at the identity boundary/base pair contractible. Applying the universal property in the opposite comparison direction and to the two composites gives inverse homotopies, so every specified comparison in this fibre is an equivalence at the vertex. Both cones must be relative limits with identical boundary and base: these hypotheses are stated. The canonical Cartesian edge already supplies the comparison in the parent proof. The lemma includes an arbitrary small, possibly empty, boundary and asserts no product existence.

For inert-projection detection I read the symmetric output-product axiom and the reduction using Remark 2.1.2.9 on p. 268. Forward detection is cocartesian composition. Conversely factor through a chosen cocartesian lift of the inert base map. The output composites make all unary components of the intervening map equivalences, and the Segal equivalence detects equivalence in the target fibre. Its composition with the lift is cocartesian. With zero outputs that target fibre is terminal, so the comparison remains an equivalence. The statement requires an inert base map; it does not assume active cocartesian transport or that every edge is cocartesian.

I checked the identity cylinder; empty D (both indexing categories empty); ordinary nerves (the slice models give usual factorization categories); unary fibres with noninvertible arrows; identity Cartesian edges and distinct equivalent lifts; empty and singleton cone boundaries; and nullary outputs. Empty colour categories still have the operad's arity-zero object. No Kan colour hypothesis, presentability or active transport was added. New node statements remain unchanged by these checks.

## Searches

Whole-DAG searches covered cylinder, two limit cones, relative uniqueness, comma/slice, inertness iff projections and Cartesian equivalence. Whole-blueprint searches used Cartesian cylinder, relative product, inert projection, limit cones, Cartesian edge and factorization categor. Relative-product hits were geometric Künneth theorems, not relative cone comparison. The ancestor tool returns prop-coef-integral-exceptional-adjoint; its current paragraph 2 is the finite-coefficient mapping comparison recorded in the item's ancestry. All new nodes retain the full ancestry via this item, including the existing intermediate nodes. No blueprint node states an extracted lemma, and no chapter or unit route is changed.

All recorded new-node searches were run with msearch.py and their results read. The retained second semantic phrasings for inert detection return ordinary nerves, inertia, and unrelated splittings. Fresh searches for Cartesian-edge and relative-cone comparison return ordinary Cartesian-lift uniqueness (Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean, domainUniqueUpToIso at line 141), ordinary IsLimit uniqueness (Mathlib/CategoryTheory/Limits/IsLimit.lean, lines 143 and 159), and strict Segal fillers. I opened these source statements: they quantify over ordinary categories, not the quasicategorical relative interfaces required here. Cylinder-slice searches return ordinary structured-arrow equivalences (Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.lean, isEquivalence_post at lines 339 and 816), categorical pullbacks of ordinary categories, and Brown cylinders. None states the comparison of coherent slice models. Consequently no hit is a one-line specialization. Historical item searches are preserved unchanged. The log is preserved even for exploratory searches not used by a node; no unrun query was added.

## Not duplicates

- lem-coef-symmetric-cartesian-cylinder-slice-comparison vs lem-cbc-relative-coslice-left-fibration: the existing node gives left fibrations of join-coslices, not the cylinder and iterated-slice equivalences with F_g.
- lem-coef-symmetric-cartesian-cylinder-slice-comparison vs lem-coef-infinity-cartesian-mapping-fiber: a mapping-space equivalence at one edge does not state the indexing/factorization quasicategory comparison.
- lem-coef-symmetric-cartesian-cylinder-slice-comparison vs lem-coef-simplicial-right-fibration-presentation: the existing fibrewise criterion does not supply the comparison or the F_g identification.
- lem-coef-symmetric-cartesian-cylinder-edge-comparison vs lem-coef-infinity-cartesian-mapping-fiber: the extraction states coherent uniqueness of lifts and equivalence of the intervening edge, rather than only the mapping-fibre formula. The human explicitly requested extraction from old Step 10.
- lem-coef-symmetric-relative-product-comparison vs def-coef-infinity-relative-cone: the existing node defines the universal-square predicate; this extraction states coherent uniqueness of relative universal cones.
- lem-coef-symmetric-relative-product-comparison vs lem-coef-infinity-relative-cone-equivalence: the existing node preserves universality under an already given equivalence; it does not produce an equivalence of apices from their relative universal properties.
- lem-coef-symmetric-inert-projection-detection vs lem-coef-symmetric-operadic-fibration-recognition: the existing node states operad axioms and pattern-fibration recognition, not this arrowwise detection theorem.

These are the specific non-elementary comparisons requested by the return, not elementary regroupings or copies of the parent conclusion. No new node has a Stacks tag, so there is no duplicate tag pair.

## Review by NJ

I compared the current shared repository with the retained sandbox, confirming that statement and Lean record stay identical. I read the chapter, assigned unit, SETUP's three levels, stage-1 brief, dag-sync, GOAL and delivery-errors B–E. The Q67 report is retained as historical evidence; this is my review of the repaired result. I read the official HA proof through both (a) and (b). Only part (1) is used; its part (2) Kan-colour argument is excluded.

Step 1: I opened exponentiation and isofibration-pullback-limit; they give the functor isofibration and identify strict fibres with categorical pullbacks. Pointwise-equivalences supplies the inverse natural transformations. Symmetric recognition and cocartesian mapping/composition provide lifts of base bijections and invariance of local projections. This verifies witness transport without assuming f is itself a fibration.

Step 2: full-essential-image supplies a coherent inverse after the written unary fully faithful and essentially surjective calculation. The unary pointed set has only the identity automorphism. This justifies strict unary fibres without claiming the analogous fact in higher arities.

Step 3: I opened symmetric-recognition, join-cone-calculus, homotopy-fibre-detection, pullback-pasting, relative-cone and cocartesian-mapping-criterion. They supply the displayed product mapping equivalence and relative-limit square. Fibre detection is used over the identity base equivalence, meeting its hypothesis. The empty product is explicit. The returned proof step is retained.

Step 4: Cartesian mapping-fibre and Cartesian-colimit-localization give the cross-fibre mapping formula and the equivalence of entire functor categories including noninvertible transformations. The colimit of the one-arrow diagram is P. Exponentiation and strict-pullback statements justify the strict endpoint/base representatives. Thus r satisfies every assumption of the new slice-comparison node, including inversion of Cartesian edges.

Step 5: I checked the new slice-comparison statement word for word: its K-to-K' and comma-to-F_g equivalences are exactly those applied. Weak contractibility comes from the parent's explicit hypothesis. The opposite comma criterion applies to these small comma categories; relative-cone duality supplies the orientation. Join-cone and cofinal-relative-join-slice-restriction give preservation/detection of relative universality and strict boundary/base extensions. I_x remains full, not restricted on comparison arrows.

Step 6: cocartesian composition/initiality and its mapping criterion apply after pullback along the fixed colour-projection edge, precisely where the lift is locally cocartesian. The full subcategory contains that initial lift. Initial-components and right-Kan-universal-restriction state the required pointwise test; symmetric recognition gives the product axiom used in Step 3, and join-coslice gives the indexing model. The initial family may be empty.

Step 7: cocartesian mapping, join-coslice and join-cone give the displayed mapping fibre. The unary equivalence from Step 2 makes its preceding map an equivalence, hence the fibre contractible. Initial-components provides exactly existence and detection of the limit. Symmetric recognition explicitly includes the empty product for arity zero.

Step 8: I read both clauses of right-Kan-universal-restriction. Its cone comparison passes J to I; repaired Step 5 and cofinal-relative-join-slice-restriction pass I to K. Initial-components gives the cone at vertices in D. The full restriction theorem applies to D full in E and the isofibration Q→S from Step 1. No completeness assumption appears.

Step 9: localization gives composition with r; mapping/composition criteria preserve inertness under coherent equivalences. The established inert-leg criterion and the right-Kan statement give the forward implication. This step was lost in the interrupted edit and is restored verbatim.

Step 10: the two relative product cones have the same boundary A_0(d_i), same base projection cone, and the canonical Cartesian edge as a coherent comparison. The new relative-product statement therefore applies. The new Cartesian-edge statement covers arbitrary cross-fibre lifts and degenerate-base Cartesian edges. This establishes condition (ii) without hiding the comparisons inline.

Step 11: I read the new detection statement and existing cocartesian mapping/composition statements. The chosen projections and their composites with v are inert in P. Steps 7–8 make their A-images inert; Step 10 inverts the Cartesian comparisons. The projection family at A(y) is thus cocartesian and every composite with A(v) is cocartesian. Those are exactly the detection lemma's hypotheses, including its empty-family clause.

Step 12: right-Kan-universal-restriction states a trivial Kan fibration on all transformations and higher simplices; its boundary-lifting property persists over the full permitted-boundary subcategory. Steps 8–11 identify its domain with X. Composition with the localization section A↦Ar and with e gives exactly restriction by f. This is the retained closing argument with updated references, restoring the interrupted attempt's missing conclusion.

B1–B10: each new node introduces its objects and defining notions, has no proof sketch, has proper mathematical TeX, actual searches, complete ancestry, and no exact Mathlib/project attachment. C1–C8: every external non-elementary input is a cited statement; citations.json quotes each verbatim; a reachability traversal of the DAG overlay found no dependency path back to the item. The generic coslice tool from another unit remains in split_report.tool_uses; no new maintainer-owned field is added. D1–D5: the extracted comparisons are strictly smaller than the item, and the right-Kan construction and final equivalence remain proved in its steps. E1–E6: sizes, fibrations, equivalences, nullary cases and exact cone boundaries were checked, and the iterated-slice models are compared by equivalence rather than silently identified. E7: the retained source terminology correction (initial, not final, in this ordered coslice convention) is explained in the historical report and does not change the statement.

## What remains

The required server dry run passed at 9454eefcd9, printing OK (not pushed): preflight passed, and exited successfully. It checked the repaired item and four new statement-only nodes, including check_dag and review_split. The single queued invocation was polled throughout and no duplicate delivery was started. The authorized direct push follows; its own preflight checks this complete report as well. No mathematical work remains in this stage-1 repair.
