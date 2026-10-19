# Worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-cat-infinity-colimits-cartesian-closure.json: repaired stage-1 split, ten steps; statement, statement dependencies, blueprint ancestry, Lean record and historical searches retained.
- dag/nodes/sec-six-functors/lem-coef-small-inner-horn-completion.json: new statement, unsplit; no Mathlib match after two phrasings and semantic, Loogle and source searches.
- citations.json: one verbatim statement excerpt for every cited node of every item step. Where a step uses several clauses, the whole statement is included to avoid omitting its hypotheses.
- searches.jsonl: actual msearch.py records, retained as emitted.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout for the blueprint tag, catInfinity_limits_colimits_cartesianClosed, CatInfinityLimitsCartesianClosed, quasicategorical colimits, inner-anodyne replacement and Cartesian closure. No declaration proves all clauses. The recorded Sheaf theorem is not evidence of a finished WeilConjectures declaration and was not edited or compiled.

## WANTED

WANTED: archived Lurie, Higher Topos Theory, especially Corollaries 2.2.5.4 and 2.3.2.4–2.3.2.5, Sections 3.1.3–3.1.4 and 3.3.3, Proposition 5.2.4.2, for the item and lem-coef-small-inner-horn-completion. Read the online IAS PDF.

WANTED: archived Cisinski, Higher Categories and Homotopical Algebra, Theorem 6.6.9, Remark 6.6.11, Theorem 7.3.22 and Proposition 7.3.23; archived Kerodon Tags 01F1 and 033R, for the unchanged surrounding foundations. The online Cisinski PDF was read; Kerodon HTML did not expose the mathematical body to the browser, so the latter tags are inherited citations checked through their DAG statements rather than claimed independent source readings.

## Faults and repair

The dedicated Q110 return identifies step 3 (2027 characters) and step 4 (3427 characters). Step 3 hid a reusable construction: small inner-horn completion with a restriction map lifting against every monomorphism, uniformly against larger targets. This is now the statement-only child lem-coef-small-inner-horn-completion. The item still proves the core comparison from the restriction theorem, the Joyal weak factorization system, the quasicategory equivalence characterization and componentwise equivalences.

Step 4 repeated a path-space transport proof already contained in the statement of lem-coef-infinity-terminal-pullback-criterion: its comparisons are invariant under equivalences of diagrams. The repaired step retains the factorization, pushout and restriction calculation, and applies this precise existing invariance clause to (q,1_B,1_C), in the opposite category. No new transport lemma is needed. The original ten-step route is retained; no statement or Lean-interface correction is made. Steps 3 and 4 now have 1339 and 1644 characters; every step is below 2000. The other long-step candidates were inspected, not merely truncated.

## Not duplicates

lem-coef-small-inner-horn-completion vs lem-coef-simplicial-shape-categorification: the latter asserts existence of a same-universe categorical equivalence and functor-category equivalence; it does not assert a specified inner-horn cell construction, lifting against all monomorphisms, or lifting against arbitrary larger-universe inner fibrations. The child states exactly these stronger, construction-specific inputs. The existence-only conclusion was not copied as a new node. Moreover the categorification node's statement dependency def-coef-complete-algebroid reaches this item (via kan-relative-nerve-left-fibration, space-valued-straightening, unmarked-relative-nerve-cone-comparison, model-infinity-derived-adjunction, cosimplicial-frame-mapping, hammock-infinity-localization and infinity-functor-pushout), so citing it here would introduce a cycle.

lem-coef-small-inner-horn-completion vs lem-coef-horn-completion-point-colimit: that node fills all horns and gives a Kan weak homotopy equivalence; the new child fills only inner horns and gives the internal-functor restriction lifting property into quasicategories. Filling outer horns would change the categories under consideration.

lem-coef-small-inner-horn-completion vs lem-coef-inner-anodyne-pushout-product: that Mathlib leaf proves stability of a given inner-anodyne map under pushout products; it does not construct a small quasicategory replacement. The new child's statement uses its definition of inner anodyne; its eventual proof uses its theorem.

lem-coef-small-inner-horn-completion vs lem-coef-cat-infinity-colimits-cartesian-closure: the child concerns arbitrary simplicial sets, cell inclusions and lifting, not a clause of completeness or Cartesian closure of Cat infinity. The item still constructs its pushouts, pullbacks, exponentials, coherent adjoints and universe-preservation comparisons.

Whole-DAG statements were searched for inner-horn completion, replacement, restriction and core comparisons. Whole-blueprint searches used quasicategory, inner anodyne, inner horn, horn, completion, replacement, core, pushout, cartesian closed and small colimits. The ancestor command confirms prop-coef-integral-exceptional-adjoint; no blueprint statement matches the child or the item. The above are the nearby candidates, all read before creation. No Stacks tag states the new theorem; no SGA source is used.

## Review by Q110

I read the contract, the worker brief, stage-1 rules, delivery-errors B–E in full, the three blueprint levels, GOAL and dag-sync. I read the sec-six-functors chapter and sk-prop-sf-biduality-general unit records. I read main-20261015's prop-coef-integral-exceptional-adjoint statement and proof, now under sk-thm-sf-package: the derived coefficient-adjunction calculation in proof paragraph 2 and the following unit/counit compatibility sentences are the inherited foundation route. This repair remains below that route and does not change its coefficient categories or geometric assertions.

For sources I read HTT Section 3.3.3's introductory paragraph (printed p.214), Corollary 2.2.5.4's use of inner-anodyne replacement, Corollaries 2.3.2.4–2.3.2.5 (printed pp.100–101), and Proposition 3.1.4.2 with Corollaries 3.1.4.3–3.1.4.4 for the Cartesian marked model. Proposition 5.2.4.2 gives the pointwise representability criterion used later. I read Cisinski Theorem 6.6.9 and the small-product/pullback existence and preservation criteria in Theorem 7.3.22 and Proposition 7.3.23. The proof remains marked agent-written, including its explicit completion construction; the online source does not spell out all the universe bookkeeping. The new child is statement-only, with neither a hidden proof in its statement nor proof dependencies. Its future proof uses the original step-3 small-object argument: attach every inner horn countably, use finite generation to factor horns at a finite stage, extend lifts recursively in any larger universe, and transpose the pushout-product lifting problem. This sketch belongs here, not in the unsplit node.

I opened and read every statement cited in the item:

1. The marked-point-model node specifies the exact Kan enrichment Fun(B,E)^core, its composition and Cat-infinity coherent nerve. The coherent-nerve-comparison node supplies mapping-space comparison for a locally Kan simplicial category. The enrichment is Kan because the marked model says it is a simplicial model on fibrant-cofibrant objects; it is not the non-Kan unmarked internal Hom.
2. The diagrams-cones definition gives degreewise products, equivalence witnesses and internal Hom. The product/coproduct calculations are explicit in the step, including horn connectedness and inverse witnesses. The two mapping-space comparison nodes identify those calculations with Cat-infinity mapping spaces. The cone-calculus node supplies the missing logical passage to limiting/colimiting cones for discrete shapes, including the empty shape.
3. The new completion node now supplies exactly the small replacement and uniform lifting assertion. The Joyal-model node says cofibrations are all monomorphisms and identifies the right orthogonal class as trivial fibrations. The characterization node provides the quasi-inverse with coherent inverse equivalences, since both internal Homs are quasicategories. Cone calculus says equivalences of transformations are componentwise; this justifies the homotopies landing in the cores. The definitions provide the triangles and core convention.
4. The Joyal-model node provides the factorization in the small universe. Its fibrant-object characterization and the quasicategory-characterization node make A' fibrant and q an equivalence. The exponentiation node applies because B into A' is monic. The isofibration-pullback-limit node applies to the three functor quasicategories with no condition on the second map, and its Q=point formula is exactly the core comparison. The square criterion in the opposite category supplies the pushout and explicitly includes diagram invariance; (q,1,1) meets its equivalence hypothesis. Thus the lengthy inline transport was unnecessary and is replaced by the actual statement that says it.
5. The Joyal factorization makes A' to B a fibration between fibrant objects, so its isofibration characterization applies. The pullback-limit node allows any other leg, including empty pullbacks. The original cone is handled by the square criterion's diagram invariance. I retained the explicit maps and comparison in this step.
6. The small-colimit-generation statement is for all small simplicial shapes, not only nerves, and does not impose local smallness or presentability. Products and pullbacks from steps 2 and 5 meet its opposite hypotheses; coproducts and pushouts meet its direct hypotheses.
7. Cone calculus gives functor-quasicategory closure for any simplicial source. The explicit degreewise currying and inverse formulas retain all transformations; smallness is a set-of-maps calculation in the fixed universe.
8. The marked model and coherent-nerve comparison turn the core exponential identity into the relevant mapping-space identity. The pointwise-adjoint statement assembles these representations; a sufficiently large pair of universes makes its mapping-space size hypothesis valid. Evaluation is the displayed counit, and step 2 gave the actual product.
9. The cone-calculus statement includes the mapping-space limit criterion and contractibility of choices; the pointwise-adjoint criterion gives both adjoints to the constant-diagram functor. The two categories fit in one larger universe; no large category is silently assumed small in the original universe.
10. The completion child's larger-universe lifting assertion, invoked through step 3, is precisely what makes the same small pushout still universal against larger targets. The isofibration and pullback statements are used in the containing universe. The small-colimit-generation preservation clause then applies, and its opposite gives limits. Currying is unchanged degreewise. No replacement is assumed enriched without proof.

The tool citation lem-cbc-enhanced-functor-cone-calculus was already accepted as a generic foundation from the other unit and remains declared in split_report.tool_uses. No new off-unit tool is introduced. I preserved maintainer-owned metadata.

I tested the child on X empty, a point, an inner horn, and a non-Kan nerve: the empty construction adds no simplex; a point remains a small quasicategory (the specified algorithm may add redundant simplices); an inner horn gains fillers; filling only inner horns does not force outer horn fillers. For E empty, either both functor sets are empty (X nonempty), or both are points (X empty), so the lifting assertion is consistent. For the item, the empty product is a point, empty coproduct is empty, an empty middle span gives a coproduct, and Fun(empty,E) and Fun(A,point) are terminal. Universe enlargement keeps the finite horns and cell indexing sets fixed.

I checked B–E point by point: self-contained statements and definition dependencies, TeX escaping, actual logged searches with second phrasings, no invented Stacks tag, no new Mathlib match without source evidence, complete blueprint ancestry, no attachment based on a sorry, no reliance on a cited proof instead of its statement, no omitted non-elementary input, no statement weakening, no relabelled clause of the item, and no route change. The overlay dependency audit finds no cycle returning to either delivered node. citations.json contains verbatim passages copied from the statements read. No Lean file was written and no compiler, Lake or build tool was run.

## Unfinished work

The one new child is intentionally unsplit, as required for a one-level split. Its later splitting is a queue item, not unfinished work on this delivery. Required server dry run and push follow this report; the final tool result records their outcome.
