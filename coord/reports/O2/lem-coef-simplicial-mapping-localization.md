# Stage-1 worker report

Item: lem-coef-simplicial-mapping-localization. Group: N2. Date: 2026-10-17.

## Files written

- dag/nodes/sec-six-functors/lem-coef-simplicial-mapping-localization.json: statement, now split into six steps; statement unchanged; not a Mathlib leaf.
- citations.json: six entries, one for every cited node in every proof step, with verbatim statement excerpts.
- searches.jsonl: actual results logged by msearch.py; the item's earlier search records are retained and the current searches appended.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed because this supporting prerequisite is not the unit's key node.

## Attachments

None. Read-only searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint tag and id, simplicial mapping/localization terminology, cofibrant, bifibrant, simplicial model, and homotopyClassToHom found no project declaration stating this item. Its id has no entry in dag/lean_names_upstream.json. The corresponding master checkout search also found no declaration of the item. No upstream sorry declaration was treated as a proof. The item currently has no lean_audit entry to follow.

## WANTED

None. The proof is explicitly agent-written, following the ordinary replacement argument prescribed by the item's existing source place and the original projective-model proof Step 15. No absent literature is asserted to contain a proof.

## Defects and corrections

The unsplit item had no proof, but its statement is sound as written. It explicitly assumes the *conclusions* of the ordinary bifibrant-localization node. We use that equivalence, rather than silently assume or reprove its recognition hypotheses, and do not claim an infinity-localization result. The extra saturation conclusion is not needed here. The current item already gives an explicit from.place and ancestry; both were retained. There is no statement dispute or route change.

A potentially circular shortcut was excluded while designing the proof: equality of components in Map(P,Y) cannot first be identified with equality under q, since that is precisely what is to be proved. Step 4 therefore defines a comparison abstractly from three established bijections, and step 5 proves its value on *each actual vertex* using two strict lifting squares. The factorization f = p h i holds as actual arrows, so that identifying the comparison with q does not presuppose descent along simplicial paths for non-bifibrant objects.

## Searches and Mathlib verdict

The retained earlier records are those of the worker who created this prerequisite. All additional queries in the item are exactly the current msearch.py log entries, whose hits were read. The current searches were:

- leanfinder: In a simplicial model category connected components of the enriched mapping simplicial set from a cofibrant object to a fibrant object are the morphisms in the ordinary localization at weak equivalences
- loogle: "SimplicialCategory", "Localization"
- grep: pi0|π₀|SimplicialCategory|Simplicial.*[Hh]omotopy (AlgebraicTopology/ModelCategory)
- leansearch: Connected components of simplicial mapping spaces from cofibrant to fibrant objects give morphisms in the homotopy category
- leanfinder, second phrasing: Enriched hom space pi zero equals localized Hom for cofibrant source fibrant target in a model category via trivial mapping fibrations
- grep, second phrasing: homotopyClassToHom|leftHomotopyClassEquiv|homMk_surjective|homMk.*[Bb]ijective|homRel (AlgebraicTopology/ModelCategory)

All services answered successfully. Read Mathlib/AlgebraicTopology/ModelCategory/FundamentalLemma.lean, especially lines 34–118, and BifibrantObjectHomotopy.lean, especially lines 148–159. The former's bijective_rightHomotopyClassToHom and bijective_leftHomotopyClassToHom use ordinary model right/left homotopy quotients; the latter's HoCat.homEquivRight has the same quotient domain. Neither states the comparison with pi_0 of the specified simplicial enrichment. That conversion is mathematical work, so these hits are not an exact match or one-line specialization. No leaf is claimed. The second phrasing confirms that the homRel and BifibrantObject hits do not supply the missing enriched comparison.

## Not duplicates

No new nodes were created. Searched the whole DAG by simplicial mapping/localization, bifibrant, and component terminology; inspected the statements matching both cofibrant/component and localization notions, notably the existing bifibrant-localization prerequisite and derived-hom-adjunction sibling. The former covers bifibrant endpoints only and is reused; the latter assumes this component comparison and cannot prove it without circularity. Ran tools/blueprint_refs.py ancestor for this item and whole-blueprint search for "mapping components", "bifibrant", and "simplicial model"; none of the blueprint searches found an equivalent imported node. same_as remains empty. The exact existing ancestor and full via list are retained. No Stacks tag is asserted for this homotopy-theoretic result, and no SGA source is cited.

## Review by N2

I read the item's whole statement and source place, the source file literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md (paragraph 2 and its derived coefficient-adjunction display), the parent projective-model-calculus proof Step 15, and the whole statement of each of the four cited nodes. I also read dag/chapters/sec-six-functors.json and dag/units/sk-prop-sf-biduality-general.json. The six steps supply the ordinary mapping-component prerequisite below the existing coefficient-adjunction ancestry and do not replace a unit step. This is an agent proof; the blueprint paragraph supplies the intended application, not a falsely attributed published proof of this prerequisite.

Step 1 uses lem-coef-simplicial-boundary-collapse-test specifically for the two functorial weak factorization systems, their mutual lifting descriptions, and the definitions of cofibrant/fibrant. Factoring P to the terminal object gives the trivial cofibration i; factoring the initial object to Y gives the trivial fibration p. I checked both *additional* bifibrancy claims: A is cofibrant because P already is, and B is fibrant because Y already is. The two-filler closure argument is written explicitly as an elementary consequence of the lifting definition, not hidden behind a properness or replacement theorem.

Step 2 uses def-coef-simplicial-tensor-cotensor for its two enriched representing isomorphisms. Its statement really identifies underlying arrows with vertices and supplies the isomorphisms of simplicial sets. Taking n-simplices gives Hom(Delta^n tensor U, terminal) and Hom(initial, V to the Delta^n), both singleton sets. This justifies the terminal mapping sets in the two corner targets; ordinary initial/terminal objects alone would not justify that enriched claim. The reduction of the pullback targets is then elementary.

Step 3 uses only the SM7 corner-map axiom explicitly assumed in the item's statement and the definition of weak homotopy equivalence in lem-coef-kan-quillen-right-proper. I verified that the weak input is i for the first corner map and p for the second, while the other inputs are respectively B to the terminal object and the initial object to P, known fibrations/cofibrations from step 1. A trivial mapping fibration is a weak homotopy equivalence; the cited node defines that to include a bijection on path components. Thus the component bijection is a direct specialization of the assumption and definition, with its actual formula shown. No general mapping-invariance or Brown lemma is silently used.

Step 4 uses lem-coef-simplicial-bifibrant-localization for exactly what its statement says: H has mapping components as Hom sets, inclusion followed by q descends, and H to L is an equivalence. Both endpoints A,B satisfy its bifibrancy requirements. The item expressly assumes this conclusion, so its conditional recognition theorem is not applied without verification. The actual map on arrows is q(h). Inverting i and p is part of the explicitly given finite-string localization, and the inverse of Hom-set transport is displayed. This is the single non-elementary step, citing an existing prerequisite rather than a new node restating the item.

Step 5 uses the diagonal-lifting clauses of lem-coef-simplicial-boundary-collapse-test, not an unrecorded theorem about homotopy classes. I checked the lifting pairs (initial to P, p) and (i, B to terminal) with their required cofibration/trivial-fibration and trivial-cofibration/fibration hypotheses. The square commutativities follow from uniqueness out of the initial object and into the terminal object. The resulting equalities pg=f and hi=g give p h i=f exactly; substituting into the constructed bijection proves it is induced by the specified q. This repairs the possible circular identification noted above.

Step 6 uses the enrichment/vertex conventions of def-coef-simplicial-tensor-cotensor. Precomposition and postcomposition are simplicial maps, hence act on components. The displayed vertex equality under q proves naturality because every component has a vertex, as specified by the component convention in the bifibrant-localization statement. For composition I checked the middle object is both cofibrant and fibrant, so all three comparisons used are defined. The identity and composition equalities are just q's functor laws. No natural replacement choices or natural fillers are assumed; the vertex calculation makes them unnecessary.

I checked delivery-errors B–E against these files: no new statement-only node to audit under B1–B9; all statement dependencies remain definitions/conventions or the expressly assumed comparison; the attachment search rules in B10 were followed. Every use has a verbatim citation entry and each cited statement was read (C1–C4); no dependency on a child/citer was added and the parent is not cited (C5–C8). There is no relabelling or relocation into a new lemma (D1–D5). The lifting, enrichment and source/target hypotheses are checked above, and the argument identifying the actual comparison is fully written rather than called a transport (E1–E7). No off-unit tool declaration is needed. All six steps are below 2000 characters; the longest non-elementary step is 1060 characters and contains only the application of the existing equivalence and explicit inverse formulas, with no hidden lemma.

Small cases checked: if Map(P,Y) has no vertices, the two mapping weak equivalences and the bifibrant equivalence force the localized Hom set to be empty too; no vertex is chosen before quantifying over f. If a replacement is an identity or P,Y are already bifibrant, the formulas still give q(f). Empty simplicial mapping sets cause no problem for the weak-equivalence component definition. The initial and terminal objects need not coincide. No assumption of properness, combinatoriality, local presentability, nonempty Hom sets, or enriched functorial replacements was introduced. Universes are exactly those already enlarged in the item.

## Unfinished work

None in this one-level split. The existing bifibrant-localization prerequisite remains a separate item; its conclusion is an explicit assumption of this item, not an unproved assertion concealed in the proof. Required server dry-run and final delivery results will be recorded after they complete.

## Dry-run repair

The first server dry run exited with one B2 wording diagnostic in step 4: the phrase “the item's” was not suitable for a standalone node. Replaced it with the explicitly named finite-string localization q and named the assumed bifibrant-localization conclusion directly. Also made step 3 refer directly to the assumed simplicial model axiom. No mathematical hypothesis, statement, citation or dependency changed.
