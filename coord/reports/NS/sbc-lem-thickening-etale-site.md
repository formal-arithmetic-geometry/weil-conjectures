# Stage-1 worker report: sbc-lem-thickening-etale-site

## Files written

- `dag/nodes/sec-smooth-base-change/sbc-lem-thickening-etale-site.json`: item split into three proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node use.

## Attachments

The previously proposed attachment was refused because `AlgebraicGeometry.Etale.co` was not a declaration of the project. I therefore did not answer ATTACH. The exact source declarations remain represented by existing DAG nodes and are used only through those nodes.

## WANTED

None.

## What was wrong in the previous attempt

The item was treated as an attachment, but the delivery checker rejected the malformed/non-project declaration name. The item is now split, with the thickening-to-universal-homeomorphism reduction and the site, covering, sheaf, and cohomology interfaces cited separately. The existing general universal-homeomorphism proposition is strictly more general than this thickening special case, so no duplicate node was created.

## Review by NS

I read the item source in the blueprint and the Stacks source for Proposition 59.45.4 (Tag 03SI), and checked the three existing DAG statements used by the split. Step 1 uses the statement that a surjective closed immersion is a universal homeomorphism; this exactly supplies the hypothesis needed by the general invariance results. The thickening definition in `def-sbc-first-order-thickening` supplies the closed-immersion and surjectivity interpretation used there. Step 2 uses the existing site-equivalence statement for universal homeomorphisms and the separate statement that jointly-surjective etale covering families are preserved and reflected; together these give the claimed isomorphism of sites, including coverings. Step 3 uses the existing topological-invariance proposition, whose statement explicitly gives both the equivalence of small etale topoi and the cohomology isomorphism. I verified that every citation quote is copied verbatim into `citations.json`, that all proof dependencies occur in the step uses, and that the statement remains the original thickening claim with no added hypotheses or weakened conclusion. I also checked the small edge case of an identity thickening: it is a surjective closed immersion, the universal-homeomorphism reduction is reflexive, and all three conclusions specialize to identity equivalences and identity cohomology maps. Mathlib searches found only generic etale-site declarations and no theorem for this topological-invariance statement.

## Second reading by NS

- Item statement: checked all hypotheses and clauses against Tag 03SI, Proposition `proposition-topological-invariance` in `etale-cohomology.tex` (lines 6547-6570) and the blueprint node. This is its thickening special case; "isomorphism of sites" uses the source's terminology for an equivalence matching coverings. No statement dispute.
- Step 1: read `def-sbc-first-order-thickening` and `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism` in full. The former's clause (1), not its square-zero clause (2), says exactly closed immersion plus surjectivity. The latter accepts any such immersion, so no globally nilpotent ideal or finite-order assumption is needed. Checked More on Morphisms 04EX, `definition-thickening`, and the universal-homeomorphism criterion 04DF, `lemma-universal-homeomorphism`.
- Step 2: read `lemma-weil-pbc-universal-homeomorphism-site-equivalence`, `lemma-weil-pbc-universal-homeomorphism-coverings`, and `def-weil-pbc-etale-site`. The first gives base-change equivalence on all etale schemes (04DZ, `theorem-topological-invariance`), the second matches arbitrary jointly-surjective families, and the third identifies these with coverings. Thus no faithfulness, essential-surjectivity or covering argument is taken from a dependency's proof rather than statement.
- Step 3: read `prop-weil-pbc-universal-homeomorphism-topos`, including its displayed formula. It accepts the morphism from Step 1 and gives both the topos equivalence and the natural cohomology isomorphism for every abelian coefficient sheaf and every nonnegative degree (03SI, `proposition-topological-invariance`, clauses (2)-(3)). Replaced the vague coefficient-specialization sentence by the actual formula.
- New nodes: none, so B1-B7 and duplicate/elementary-node removal have no new-node cases. Existing covering compatibility is a small tool already in the DAG, not a newly created node.
- Edge cases: the empty-scheme identity and field identity satisfy the hypotheses; arbitrary etale schemes over the empty scheme are empty. The zero abelian sheaf has zero cohomology on both sides. The dual-number immersion Spec(k) into Spec(k[e]/e^2) tests a nontrivial first-order thickening, and n=0 gives the global-section identification. No restriction on dimension, quasi-compactness, or order of thickening was added.
- Independent Mathlib searches: ran LeanFinder with "An integral radicial surjective scheme morphism induces an equivalence of categories of etale schemes and of sheaves" (8 hits: category/forgetful-functor and standard-etale declarations only); Loogle with `"etale", "Equivalence"` (5 hits: affine-site and separably-closed-field equivalences, not invariance under our morphism); grep with `radicial|homeomorph|thickening|etaleEquivalence|isEquivalence.*[Ee]tale` in AlgebraicGeometry (ordinary homeomorphism uses only). Actual results are appended to searches.jsonl. No new Mathlib leaf.
- Lean attachment check (read-only): `isEquivalence_upperStar_of_thickening` states only the Grothendieck-abelian-valued sheaf clause, not the whole item, so the split remains necessary for the site clause. The existing four non-definition dependencies carry closed slopmaster2 audit records; they are usable existing tools of the proper-base-change unit. No compiler was run and no master sorry was treated as a proof.
- Changes: explicitly cited the thickening and site definitions in their steps and regenerated every citation with the full verbatim statement (including the missing cohomology formula); corrected the erroneous 04EX source file and the mistaken "Lemma 04DY" reference (04DY is a section); supplied source labels; spelled out the cohomology identification; removed worker-written `split_report.tool_uses` because acceptance of other-unit tools belongs to the maintainer. The main statements and the three-step route are preserved; the first worker's review remains above.
- Final dry run: `deliver.py NS sbc-lem-thickening-etale-site --no-push` printed OK at e8191ed5e0. The installed tool accepts no trailing `.` argument; the requested trailing-dot invocation prints usage, so the documented invocation was used.
