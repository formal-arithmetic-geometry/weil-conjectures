# Stage-1 split: lem-coef-model-localization-detects-weak-equivalences

## Files written

- dag/nodes/sec-six-functors/lem-coef-model-localization-detects-weak-equivalences.json: statement, split in eight steps, original statement and statement dependency preserved.
- dag/nodes/sec-six-functors/lem-coef-model-localization-homotopy-classes.json: statement, Mathlib leaf. Its two clauses are HomotopicalAlgebra.map_surjective_of_isLocalization (FundamentalLemma.lean:116) and HomotopicalAlgebra.LeftHomotopyRel.iff_map_eq (same file:129).
- citations.json: a verbatim statement quotation for every node cited by every proof step.
- searches.jsonl: actual msearch.py search receipts. The node records reproduce the executed tool/query pairs and results; none of these services was unavailable during these searches.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag/id, localization/weak-equivalence terminology and model-category homotopy terminology found no project declaration proving this arbitrary-model-category assertion. The upstream master is reference material only. The new fact is in Mathlib, not an attachment of a project declaration.

## WANTED

WANTED: Mark Hovey, Model categories, Theorem 1.2.10(iv) and Proposition 1.2.8, for lem-coef-model-localization-detects-weak-equivalences. The PDF at https://ericmalm.net/ac/projects/symmetric-spectra/hovey--model-cats.pdf was read online (printed pages 11-13, PDF pages 20-22), but is not archived in literature/. Nothing was downloaded. Consequently proof_origin.by is agent: the delivered proof is written out from the model axioms and the exact pinned Mathlib lemma, and does not pretend to follow an archived textbook. There is no applicable Stacks tag for this general model-category result; no tag is fabricated and no SGA source is used.

## Findings and corrections

The original statement is correct, including arbitrary source and target. It had no proof. The original Mathlib search verdict correctly distinguished the transported weak-equivalence predicate in CofibrantObject.HoCat from isomorphism in the actual localization. Mathlib's Whitehead lemmas found by search give the forward implication (a weak equivalence has a homotopy inverse); they would not justify the converse needed here. The delivered split avoids that gap by a cylinder lift followed by retract closure.

The assigned file was absent from the shared repository's checked-out dag/nodes, but present and unsplit in the launcher's current read-only mirror /home/ubuntu/weil-nt-live-dag/nodes/sec-six-functors/. The sandbox copy was taken from that mirror. Existing statements were checked against that current DAG as well as searches in the shared checkout. The repository, live launcher, Lean checkouts and literature were not edited, and no git command or compiler was run directly in the repository.

The item is a created foundation node, not its unit's key statement, so no unit realization fields were edited. Its inherited unit is sk-prop-sf-biduality-general; its historical blueprint ancestry points to prop-coef-integral-exceptional-adjoint, proof paragraph 2. I read the chapter and inherited unit records and the current main-20261015 exceptional-adjoint proof. The ordinary model-category lemma serves the finite mapping-complex comparison; it changes no coefficient category, base-change morphism, geometric hypothesis or chapter/unit route. The model-category definition is supplied by lem-coef-model-infinity-derived-adjunction, declared as a generic tool use only for that explicitly written definition, not for the node's derived-adjunction theorem.

## Not duplicates

No same-tag pairs exist: the new source carries no Stacks tag. Searches of both DAG views, the whole blueprint with tools/blueprint_refs.py search (model homotopy, localization homotopy, cylinder, weak equivalence), and the project Lean source found no node stating the new ordinary mapping-class result for arbitrary model categories. The proposed new id was absent. The blueprint ancestor command in the shared checkout returned None because the new item is not yet in that checked-out DAG; the exact ancestry stored in the current mirror is retained and extended by prepending this item to via.

lem-coef-model-localization-homotopy-classes vs lem-coef-model-localization-detects-weak-equivalences: the leaf describes representatives and equality of localized arrows from cofibrant to fibrant objects; it does not assert reflection of isomorphisms or weak equivalences. The item's argument supplies this reflection by rectification, homotopy equations and a retract, then removes the endpoint assumptions.

lem-coef-model-localization-homotopy-classes vs lem-coef-cosimplicial-frame-mapping: the existing node describes framed infinity-localization mapping spaces and actual representatives of their components, but its statement does not identify equality in an arbitrary ordinary localization with the existence of a cylinder homotopy.

lem-coef-model-localization-homotopy-classes vs lem-coef-dgcat-model-structure: that node has a similar homotopy-class clause only for the special model category of small dg categories, not arbitrary model categories.

lem-coef-model-localization-homotopy-classes vs lem-coef-dg-module-diagram-classification: the latter classifies whole dg module diagrams by quasi-functors and isomorphism classes; it does not supply this general ordinary Hom-set statement. The simplicial model localization, simplicial Bousfield, Kan mapping, derived-category and K-injective Hom nodes found in the broader search impose enrichment or special algebraic objects and likewise do not subsume the new leaf.

## Review by Q07

I checked B-E against the actual JSON statements and sources. For the item I read the current blueprint exceptional-adjoint proof paragraph 2 and Hovey's Theorem 1.2.10(iv), plus the proof of Proposition 1.2.8. For the new leaf I read FundamentalLemma.lean in full through line 138, especially the ambient ModelCategory/IsLocalization hypotheses, the cofibrant-source/fibrant-target assumptions at 65-67, map_surjective_of_isLocalization at 116-120 and LeftHomotopyRel.iff_map_eq at 129-134. I also read the actual definitions of Cylinder in Cylinder.lean:135-136 and LeftHomotopyRel in LeftHomotopy.lean:195-196. Thus the cylinder in the leaf deliberately has no good-cylinder condition; that improvement is proved in the item rather than claimed as part of the Mathlib match. The new leaf has a self-contained statement, inline cylinder/homotopy definitions, one statement dependency defining its model axioms, no proof or proof dependencies, exact declarations/file/lines, genuine search receipts and filled blueprint fields.

Step 1 uses only the definition paragraph of lem-coef-model-infinity-derived-adjunction. That paragraph explicitly states both weak factorization systems, mutually characterized lifting classes, two-out-of-three, retract closure, and functorial factorization. The step derives composition closure and the isomorphism/identity cases by the lifting definitions. The forward implication uses the item's localization hypothesis directly.

Step 2 uses that same stated functorial factorization, not any argument hidden in the cited node's proof. I checked that RQZ is both cofibrant and fibrant, that both replacement naturality squares have the displayed domains and codomains, and that invertibility transfers without assuming u is already in W. This is precisely why there is no added cofibrancy or fibrancy hypothesis on the original endpoints.

Step 3 uses the trivial-cofibration/fibration factorization explicitly present in the model definition and the REPRESENTATION clause of the new leaf. I checked that B is cofibrant and E is fibrant before representing the inverse of gamma(p). E is also cofibrant, which is needed later. Representing an inverse in the localization does not claim an inverse in the original category.

Step 4 uses the EQUALITY clause of the new leaf for B to B, so both endpoint hypotheses hold. Its citation really promises the cylinder J and homotopy H used. I checked the construction of K, the contraction cv, and both endpoint equations. The improvement to a good cylinder is an explicit factorization of B coproduct B to J, not an unquoted theorem about choosing homotopies. The cofibrancy of B gives the coproduct injection's lifting property by lifting the other summand, and composition gives the endpoint cofibration. Its weak equivalence follows from the contraction equation and two-out-of-three. These elementary facts remain steps, not spurious new nodes.

Step 5 uses just the stated lifting axiom: its left map a_0 is a trivial cofibration and right map p is a fibration. I checked the square ps=H_1 a_0 and the two lift identities pV=H_1 and Va_0=s. The resulting t=Va_1 is a strict section because pt=1_B; its image is the inverse of gamma(p), so gamma(tp)=1 is valid.

Step 6 again uses the EQUALITY clause, now with source/target E, whose cofibrancy and fibrancy were established in Step 3. I checked that each cylinder endpoint belongs to W by two-out-of-three, then that G and tp do too. This does not smuggle in saturation or a converse Whitehead theorem: it is three applications of the explicitly cited model axiom to the displayed cylinder equations.

Step 7 uses the RETRACT-CLOSURE clause of the model definition. I checked both arrow-category morphisms, including that the second square uses ptp=p, and that the composite on p is the identity because pt=1_B. Thus p, and then pi=f, belong to W. Step 8 applies the same stated two-out-of-three property to the two replacement squares in the order RQ(u), Q(u), u. Every non-elementary input is either the new leaf or the expressly quoted model axiom; no step relies on another node's proof, on an absent Hom statement or on unspecified coherence.

Small-case checks: for identities and actual isomorphisms the forward implication and lifting arguments apply; the terminal one-object model category has only identity instances throughout. Discrete model structures with W the isomorphisms reduce to the ordinary isomorphism criterion. Models in which every map is weakly equivalent satisfy the assertion without needing properness. Neither the proof nor leaf assumes pointedness, stability, enrichment, combinatoriality, nonempty objects, properness, or a special coefficient ring. The cylinder construction uses finite coproducts supplied by the complete/cocomplete model category hypothesis, and all localizations are in the stipulated universes. No new false generalization or weakened conclusion was introduced. There is no STATEMENT-DISPUTED or source error to repair.

I compared the new leaf with the item and the nearby general/special mapping-space nodes to rule out relabelling and duplication. The item's proof carries the section, homotopy and retract argument itself; the leaf does not restate its conclusion. All citation quotes were copied verbatim from the two cited statements; proof_deps is the union of step uses. The only new edge is through a Mathlib leaf with the same model-definition dependency already in stmt_deps, so the intended dependency structure is acyclic; the required dry run checks the actual delivery overlay.

## Unfinished work

No mathematical step remains unsplit in this delivery. No new unsplit node was created. A second worker must read the accepted sandbox and deliver it; this worker runs only --no-push.


## Second reading by Q07

- Item statement: checked against the imported blueprint proof paragraph 2 and the model-category definition; all hypotheses, arbitrary endpoints, and the iff conclusion agree. Verdict: PASS.
- Step 1: checked the weak-factorization-system consequences and the localization forward direction against `lem-coef-model-infinity-derived-adjunction`; the lifting and composition arguments are written explicitly. Verdict: PASS; marked non-elementary because it is several deductions.
- Step 2: checked both functorial replacement factorizations, endpoint cofibrancy/fibrancy, naturality squares, and transfer of invertibility against the cited model-category statement. Verdict: PASS; marked non-elementary because it is a multi-part replacement argument.
- Step 3: checked the trivial-cofibration/fibration factorization and the Mathlib representation clause for the inverse with the stated bifibrant endpoints. Verdict: PASS.
- Step 4: checked the cylinder clause, the good-cylinder factorization, coproduct cofibration argument, endpoint equations, and two-out-of-three use against both cited statements. Verdict: PASS.
- Step 5: checked the displayed lifting square, the strict section equations, and the inverse calculation against the model lifting axiom. Verdict: PASS; marked non-elementary because the square is constructed and then used.
- Step 6: checked the second Mathlib equality clause and each two-out-of-three application for the cylinder equations; no converse Whitehead theorem is used. Verdict: PASS.
- Step 7: checked the arrow-category retract maps and both commutativity/composite equations against retract closure and the factorization data. Verdict: PASS; marked non-elementary because the retract argument has several equations.
- Step 8: checked both naturality squares and the two successive two-out-of-three applications transfer weak equivalence back to the original map. Verdict: PASS; marked non-elementary because it contains two separate deductions.
- New node `lem-coef-model-localization-homotopy-classes`: checked its self-contained model/localization hypotheses, both clauses, inline cylinder definition, Mathlib declarations and source lines, and all three search receipts. Verdict: PASS; exact Mathlib leaf.

Changes made: corrected the new leaf's `created.item` to this item (the worker had copied another item id), and changed steps 1, 2, 5, and 7 from `elementary: true` to `false` because the contract reserves elementary for one-line deductions. No statement, dependency, citation quote, or route was changed.
