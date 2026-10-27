# Stage-1 delivery: lem-sfb-stack-big-etale-derived-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-big-etale-derived-base-change.json`: item, statement, now split into six proof steps. Mathlib verdict: no match after the logged LeanFinder, Loogle, grep and LeanSearch queries, including a second semantic phrasing.
- No new nodes; no Mathlib leaves created. `citations.json` records one verbatim statement quotation for every step/node pair; `searches.jsonl` is the unmodified msearch log.

## Attachments

None. I searched the live `lean/WeilConjectures/` both for the blueprint tag and for algebraic-stack/big-etale/base-change notions. The hits concern schemes and small-etale base change; none states the item. No compiler or Lake tool was run.

## Wanted literature

None. The source proof and its resolution construction are available locally.

## Corrections and observations

The item statement is unchanged. Stacks Tag 075H, `lemma-base-change-higher-direct-images`, agrees with all its hypotheses: arbitrary morphisms of algebraic stacks, modules on the inherited big etale ringed sites, degree-zero F, no representability, geometric flatness, qcqs or quasi-coherence assumptions. Flatness of the associated ringed-topos morphisms is a different notion and follows from the unchanged structure rings and exact precomposition.

The inherited `blueprint.from.node` was null: `blueprint_refs.py ancestor` also returned None because the long creation chain terminates in a non-DAG Lean-module record. I repaired this field to `det-thm-sf-ctf-stability-direct-images`, the anchor explicitly named in `from.place` and already repaired in the existing moduli-groupoids definition on the same chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3), and the chapter/unit records. This split is a supporting localization input below that inherited route; it does not replace a unit step or change chapter data. Whole-blueprint searches for 075H, derived base change, pushforward restriction and precomposition found no equivalent statement: the flat-module derived base-change node found is for qc separated schemes and quasi-coherent coefficients with tensor pullback, not this result.

I did not use `lem-sfb-stack-big-etale-higher-image-base-change`: its sole proof dependency is this item, so citing it would be circular. Nor did I cite the representable-derived-restriction node, which also depends on this item. The already reviewed fibre-cohomology-presheaf formula (075G) and its test-fibre-injective prerequisite were read; the latter is the exact resolution input needed here. This avoids creating duplicate nodes for either result.

## Not duplicates

No new nodes are proposed. The underived fibre equivalence and compatibility with restrictions are written out as an elementary step, not promoted to a new node or substituted by a restatement of the desired derived assertion.

## Review by NF

I read the complete local proof of Stacks 075H and the preceding 075G (`lemma-pushforward-restriction`), the underived comparison 075B (`lemma-base-change`), exact precomposition and structure-sheaf functoriality in 06TS/06TW and `section-modules`, and `sites-cohomology.tex` 0736 (`lemma-base-change-map-flat-case`) and 07A7 (`remark-base-change`). For the resolution comparison I read `derived.tex` 013P (`lemma-morphisms-lift`) and 013S (`lemma-morphisms-equal-up-to-homotopy`). There are no new-node source statements to audit. I opened the statements of every proof dependency, rather than taking material from their proofs.

Step 1 uses the unconditional clause of `lem-sfb-stack-representable-module-injective-transport`: its statement explicitly says precomposition is exact and left adjoint to the section-formula direct image for every stack morphism. Its injective-preserving pullback clause has an additional representability hypothesis; I never use that clause for arbitrary a or b. The unchanged ring at a test object is precisely the module convention of the item.

Step 2 cites the actual groupoid 2-fibre-product definition in `def-sfb-stable-pointed-moduli-groupoids`. I expanded both categories, gave the functor, inverse and isomorphism between their composite and identity, and checked that the underlying test scheme, scheme maps, coverings and section-ring actions stay the same. Restriction along a test arrow composes the same isomorphism in Y in both constructions. The counit evaluates a compatible family, so this explicit section isomorphism is the underived mate, not an arbitrary isomorphism. This is the few-line definition argument Stacks 075B gives, with its omitted restriction compatibility supplied, and it is appropriately marked elementary.

Step 3 uses only the existence clause of `lem-sfb-module-resolution-derived-presheaf-comparison`, which is for arbitrary small ringed sites and structure-module sheaves; it is not the small-etale constant-ring enough-injectives statement. This supplies nonnegative degreewise monomorphic resolutions of F and a*F. Exactness preserves the monomorphism and its homology by `lem-sp-exact-functor-preserves-homology`. Thus every hypothesis of `lem-weil-pbc-lift-along-injective-quasi-iso` is met and its stated strict lift gives u a*r = s. No injectivity of a*I is assumed.

Step 4 checks canonicity separately from invertibility. `lem-weil-pbc-bounded-below-injectives-kinjective` applies to I and J, and the statement of `def-sfb-right-derived-functor` gives invertible units on K-injectives. `lem-sfb-flat-ringed-exchange-resolution-unit` explicitly gives the displayed unit identity for every bounded-below P, with no acyclicity hypothesis; P=I satisfies its hypotheses. Its naturality applied to u and the equation from Step 3 give exactly Q(v) after the fixed resolution identifications. This is why Step 5 proves the canonical base-change map invertible.

Step 5 uses `lem-sfb-stack-test-fibre-restriction-injectives` twice, for (f,b(y')) and (f',y'). The statement allows both morphisms to be nonrepresentable and supplies exactness and preservation of module injectives for precisely these test-fibre projections. The exact-functor homology leaf makes the pulled-back complexes resolutions. The elementary equivalence of Step 2 preserves injectivity by transporting its defining extension problem; this does not require a theorem about a new coefficient category. The restricted map preserves the augmentation. The lift lemma supplies a reverse map, uniqueness-up-to-homotopy supplies both composite homotopies, and the homotopy/cohomology leaf explicitly carries them through additive global sections. Hence v(y') is a homotopy equivalence. The section formula identifies that map before passing to cohomology. I checked the hypotheses of the uniqueness lemma: bounded-below injective target and a quasi-isomorphism augmentation. I did not take an unjustified sectionwise exactness of global sections.

Step 6 uses the statement of `lem-pur-quasi-iso-of-sections` for arbitrary ringed sites and module-sheaf complexes, in the common small-skeleton universe; it has no smoothness or purity hypotheses. It gives a quasi-isomorphism of sheaf complexes from the sectionwise test. The localization definition of the derived category inverts it, and Step 4 identifies it with the natural derived mate. This generic site lemma and the uniqueness-of-resolution-lifts lemma are declared as off-unit tools in `split_report.tool_uses`; neither changes the unit's proof route.

Small cases checked: b=id gives the identity comparison; f=id reduces to exact precomposition; the empty source has zero direct image and zero complexes; a test fibre with no objects has zero sections. For a nonrepresentable f, the test-fibre projection still satisfies the existing injective-restriction statement, while arbitrary a need not preserve injectives and is never asked to do so. A closed immersion b can fail geometric flatness but has exact big-site precomposition; thus no flatness assumption was silently added. Coefficients remain all structure-module sheaves at every step, with no switch to quasi-coherent, cartesian, small-etale or constant coefficients.

I checked B1-B9: no new statement-only-node issue, no new definitions, complete TeX, source tags/labels read, no invented search records, no Mathlib leaf claim, and explicit blueprint references. C1-C8: all non-elementary inputs are node citations; quotations are verbatim statement clauses; no dependency cycle leads back to the item; the two generic off-unit tools are declared. D1-D5: the proof carries the fibre equivalence and the resolution argument itself; nothing is moved to a new node, and the source's omitted restriction compatibility is supplied. E1-E7: the module, exactness, representability, boundedness, universe and canonical-map hypotheses were checked above. No statement dispute or source error was found. All non-elementary steps are shorter than 2000 characters, and none hides a new comparison lemma: the resolution-unit comparison and injective-preservation facts already have existing nodes. The server review_split preliminary check passed with zero new nodes.

## Unfinished work

None in this one-level split. The cited unsplit inputs remain existing DAG work items; I have not split them or edited their files.
