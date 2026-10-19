# Q57: lem-pur-composition-comparison-scalar-compatibility

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-composition-comparison-scalar-compatibility.json: statement item split into six steps; not a Mathlib leaf.
- citations.json: fifteen step/node pairs, with the complete verbatim statements of the cited nodes.

Zero new nodes; zero Mathlib leaves. The statement, its hypotheses, statement dependencies, origin metadata and blueprint ancestry are retained. Only the sandbox was written. The sandbox initially contained only dispatch markers, with no node, report, search log or delivery receipt; process inspection found no active delivery for this item. Thus there was no completed interrupted mutation to repeat.

## Attachments

None. Searches of the read-only slopmaster2 WeilConjectures source for the item tag and for purity/composition and exceptional/scalar notions found no exact declaration. Smooth/Basic.lean:350–379 has nonempty_iso_dualizingComplex_comp, an existence statement for dualizing-object additivity. It neither states the coefficient equation for the specified exceptional composition comparison nor identifies its counit-normalized scalar comparison, so it cannot attach this item.

## Wanted sources

None. The proof is marked agent-written: the current blueprint supplies the transport route, and the additional argument is the explicit natural-transformation calculation using existing DAG statements.

## Findings and corrections

The item was an unsplit auxiliary extracted from the returned rational-coherence parent. Its statement is well typed in the directions given. The proof must identify the actual composition map before conjugating it, rather than define a replacement map. Step 2 transports the integral composition-coherence equation, and Step 3 pins down b by its stated counit normalization. Steps 4–6 then prove the scalar equation. No statement dispute or source error was found.

The finite-Tor restriction of integral purity cannot silently be applied to arbitrary rational lattices. Step 1 explicitly uses the existing integral stratified-perfect characterization and integral residue-Tor theorem to bridge the domains. No assertion that equality is detected by finite reductions is used. The specified integral coherence, not a uniqueness claim about arbitrary lifts, is the input of Step 2.

The original node's four inherited Mathlib searches are retained. The new searches were actually run through msearch.py and are recorded verbatim from searches.jsonl. Two LeanFinder phrasings, LeanSearch, Loogle and two Mathlib grep searches were read. The first Loogle query used an unknown identifier and is recorded as inconclusive; the later valid naturality query succeeded. LeanFinder found ordinary scheme pullback and pseudofunctor comparisons; LeanSearch found restriction-of-scalars naturality, presheaf module pullbacks and unrelated manifold pullbacks. I read Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:126–159, Algebra/Category/ModuleCat/ChangeOfRings.lean:244–286 and AlgebraicGeometry/Modules/Sheaf.lean:239–280. They do not state this constructible exceptional comparison or the smooth purity scalar square. Generic naturality is used only as an elementary calculation, so it does not need a new Mathlib node.

## Not duplicates

No new nodes. Whole-blueprint searches for scalar compatibility and pullback composition, and DAG searches for scalar/composition and counit-normalized comparisons, were made. The finite composition theorem, integral coherence proposition, scalar-naturality theorem, and scalar-extension package already provide the non-elementary inputs and are reused. The ancestor is prop-pur-rational-purity-trace-coherence, whose proof paragraph and unit Step 3 are precisely this item's route. No unit or chapter file is changed.

## Review by Q57

I read delivery-errors B–E in full, the smooth-purity chapter and purity-transport unit, and the current main-20261015 proofs of prop-pur-rational-purity-trace-coherence, prop-pur-adic-reconstruction-trace-coherence and thm-pur-rational-and-qbar-purity. I also read the finite composition statement and its current blueprint proof in sk-prop-sp-composition. This follows the prescribed lecture-notes purity route through the existing coherence statements; no SGA source was used.

Step 1 uses six opened statements. Finite type over the noetherian field gives noetherian schemes, and finite-type dimension finiteness gives finite-dimensional schemes. The raw rational-category definition says explicitly that the objects are integral objects. The stratified-perfect characterization explicitly identifies its integral category with the derived-complete category on these schemes. The residue-Tor theorem explicitly gives equality of integral constructible and uniform finite-Tor categories. Finally smooth-relative-dimension permanence explicitly permits empty schemes and adds d and e. These statements have exactly the scheme and coefficient hypotheses available here, over E and L.

Step 2 uses the integral trace/coherence proposition's statement that the composition-coherence transport holds in the reconstruction situation, and the finite composition theorem's displayed formula to fix its direction. It does not use hidden details of either proof. The general rational-transport statement extends supplied functors and natural transformations, and hence preserves their equations. Rational purity identifies the resulting purity maps with those in the question. This proves c gamma = q u for the actual transported c, which is the essential identification that a mere formal choice of a conjugated c would miss. Integral coherence is taken for the specified transported purity family, as in the item's conventions and the parent route; no assertion about arbitrary lifts follows from reductions.

Step 3 uses exactly the displayed scalar purity square and the naturality, counit normalization, unit, extension-associator and shift clauses of lem-pur-adic-purity-scalar-naturality. Rational transport preserves these equations. These are actual comparison maps, not unspecified isomorphisms. The entire cited statements were copied verbatim into citations.json, so the normalization and coherence clauses are included in the quotation.

Step 4 uses the scalar-extension package's explicit composition clause for pullback comparisons. The twist definition makes the remaining check tensor reassociation of nonnegative powers; the integral operations comparison states the natural pullback/tensor scalar identifications. The proof writes the balancing formula and even-shift sign, so it does not hide a separate geometric purity lemma. This is an elementary check of the specified comparisons. It does not assume preservation for arbitrary direct images. Steps 5 and 6 contain only composition, the naturality equations already supplied in Step 3, substitution, and cancellation of an isomorphism. I checked every intermediate source and target: q maps H_f H_g to G_f G_g, A maps T_X H_f H_g to H_f H_g T_Z, and both final routes after precomposition start at T_X H_gf and end at G_f G_g T_Z.

For small cases, E=L makes a and b identity and the equation reads c=c. If f or g is an identity and its dimension is zero, the tensor powers of degree zero and functor unit comparisons reduce the same calculation without any division by d or e. For empty schemes the zero functors satisfy it; no nonempty fibre was used. K=0 gives the unique zero comparison. Ramified coefficient extensions are allowed: the argument uses integral scalar comparisons and rationalization, never flatness of an arbitrary finite quotient map. Successive coefficient extensions use the supplied tensor associators, and all shifts moved past twists are even. The final equality is an equality of natural transformations, not just a noncanonical objectwise existence assertion.

There are no new unsplit statements to audit for hidden hypotheses or duplication (B1–B9, C5, D1–D2). The proof dependency list is exactly the union of step citations; generic off-unit tools are proposed in split_report.tool_uses, not in the maintainer-owned field. No step exceeds 2000 characters. All non-elementary inputs are existing cited statements; the elementary tensor and naturality calculations are written out. No new source was attributed to a Stacks tag that does not state it. The imported statement needs no correction. The required server dry run and delivery follow this review.

On resumption I retained the existing proof, report and all logged searches, and compared the sandbox with the current shared item: the statement, statement dependencies, source, creation record and blueprint ancestry agree. The preserved JSON had four single backslashes in the displayed normalization formula of Step 3; I doubled the JSON escapes and parsed the complete file successfully. I re-opened all fourteen distinct cited node statements and checked all fifteen step/node quotes against the current source; each is still verbatim. I also re-read the current blueprint transport and finite-composition proofs and the possible Lean attachment in Smooth/Basic.lean:361. That declaration supplies only existence of a dualizing-object isomorphism, so it does not discharge this scalar equation. The reconstruction statement expressly makes no uniqueness claim for arbitrary coherent lifts. Step 2 therefore uses its specified transported coherence family, as in the item's conventions, rather than inferring equality from equal finite reductions. I replaced generic tool-use explanations with the exact fact each step uses. No mathematical statement or search record was changed, and every proof step remains below 2000 characters.

## Unfinished work

None in the one-level split. Existing dependency nodes retain their own states and are not changed by this delivery.
