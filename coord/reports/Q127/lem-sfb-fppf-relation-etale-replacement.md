# Q127 stage-1 delivery

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-relation-etale-replacement.json`: item, now split in seven steps; statement unchanged.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-affine-groupoid-pointed-quasisplitting.json`: new statement-only node; no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-fppf-groupoid-restriction-quotient.json`: new statement-only node; no Mathlib match.
   - `citations.json`: one exact statement quotation for each of the 19 step/node pairs.
2. Attachments: none. Searched the live `lean/WeilConjectures` for the item tag, subgroupoid/quasi-splitting and quotient-groupoid terminology, and inspected the unrelated etale-replacement hits. No project declaration states this result.
3. WANTED: none; all mathematical sources used are present in `literature/stacks-project/`.
4. Imported problems: the item was statement-only. No statement correction or route change was needed. Its inherited blueprint ancestor is null; `tools/blueprint_refs.py ancestor` also reports null. Preserved that ancestry and its via list, filled precise supporting places for the new nodes, and recorded no blueprint duplicates. Read the latest chapter, unit and direct-images proof (not an old snapshot). The chapter/unit metadata reflect the inherited supporting moduli/algebraicity branch; this delivery does not alter that branch or the unit.
5. Unfinished work: the two new inputs remain unsplit as the one-level split contract requires. No Lean was written or compiled. No repository or launcher file was changed.

## Mathematical decomposition

The local input is genuinely smaller than the item: pointed quasi-splitting produces an open finite locally free subgroupoid, but gives no etale quotient replacement or quotient comparison. The other new input is the general invariance of a scheme-groupoid orbit sheaf under an fppf covering restriction, together with reflection of relation monicity. It does not assert existence of any new presentation, any finite subrelation, or any etale projection. Division is reused from `lem-sfb-divide-finite-flat-subgroupoid`; etaleness from an open unit is reused from `lem-sfb-groupoid-open-unit-etale`.

The proof deliberately does not descend local quasi-finiteness of the divided projections: the conclusion only needs their etaleness. Flatness and local finite presentation descend, the open unit descends, and the existing open-unit lemma then gives etaleness. These are exactly the relevant parts of the 04S6 route, with the unnecessary intermediate property omitted.

## Mathlib searches and reuse

Every new-node query was run through the prescribed `msearch.py Q127 lem-sfb-fppf-relation-etale-replacement` command and is recorded verbatim in `searches.jsonl` and the respective node. Both nodes have LeanFinder, a second semantic phrasing, Loogle, grep and LeanSearch searches. Services answered successfully. Read the actual hits: ordinary etale loci and smooth neighborhoods do not supply internal finite subgroupoids; dense-subsite/sheafification comparison does not give the scheme-groupoid restriction statement by a one-line specialization; manifold structure groupoids concern a different notion. Thus both new nodes are unsplit, with zero new Mathlib leaves. Retained all inherited item searches and appended this worker's item searches.

Searched the whole DAG by tags, statements and key phrases before creation, and the blueprint by `quasi-splitting`, `quasi-split`, `groupoid`, `quotient`, `restriction.*groupoid`, `04S0`, `02VH` and `02YK`. No blueprint statement is either new input. The similarly named nodal-curve quasi-splitting nodes concern branches of nodal fibres, not open subgroupoids. Read the existing division, open-unit, separatedness, monomorphism, covering, compactness and descent statements rather than citing their proofs. Checked their dependency paths: none reaches the item.

## Not duplicates

lem-sfb-affine-groupoid-pointed-quasisplitting vs lem-sfb-fppf-space-atlas-bootstrap: the existing node proves algebraicity of an arbitrary sheaf admitting an fppf space cover; the new node constructs a pointed affine etale neighborhood with a finite open subgroupoid in a separated flat locally quasi-finite scheme groupoid.

lem-sfb-affine-groupoid-pointed-quasisplitting vs lem-sfb-fppf-relation-etale-replacement: the item constructs etale relation quotient replacements on finitely many charts; the new input only constructs the finite open subgroupoid on a single pointed chart and asserts no quotient replacement.

lem-sfb-fppf-groupoid-restriction-quotient vs lem-trf-etale-relation-finding-opens: the existing node asserts a representable open immersion between quotients of flat relations; the new node asserts quotient isomorphism under a covering restriction for arbitrary groupoids and reflection of monicity, without asserting representability or openness.

lem-sfb-fppf-groupoid-restriction-quotient vs lem-trf-etale-relation-restriction-quotient: that node assumes etale projections and an etale restricting map, so it cannot apply to the finite locally free map here (which may be ramified); the new node allows arbitrary groupoids and an fppf covering and reflects monicity.

lem-sfb-fppf-groupoid-restriction-quotient vs lem-trf-etale-pullback-relation-presheaf: that node assumes etale relation projections and an etale restriction and describes presheaf section maps; the new node permits non-etale groupoids and compares their sheaf quotients along an fppf covering.

lem-sfb-fppf-groupoid-restriction-quotient vs lem-trf-fppf-generator-sheafification-comparison: that node requires an etale map of representable generators and a sectionwise injective presheaf comparison; the new node allows a non-etale fppf covering of groupoid objects, has no such presheaf-injectivity assumption, and reflects relation monicity.

## Review by Q127

I read the affine locally quasi-finite part of Stacks bootstrap.tex Tag 04S6 from the pointed-chart paragraph through the final open-unit argument, and read Tag 04S4 itself. For the first new node I read spaces-more-groupoids.tex Tag 04S0, its Situation quasi-splitting, and Definition 04RK(3). The source requires separated projections and quasi-finiteness at the identity. The item supplies local quasi-finiteness everywhere, and step 1 proves separatedness without assuming the base S separated. An open subgroupoid has the whole object scheme and unit; the finite projections in 04RK are also flat and locally finitely presented here, so they are finite locally free in the project's definition. The restriction's projection properties are preserved by etale base change and composition. This input works for general groupoids, not just monomorphic relations.

For the second new node I read groupoids.tex Tag 02VH, including the covering-surjectivity clause, and descent.tex Tag 02YK. The product of the two object covers is an fppf cover of the relation's target, and its pullback relation is precisely the restriction in the statement. This justifies reflection of monicity. Tag 02VH applies to groupoid orbit presheaves even before relation monicity is known; the fppf covering hypothesis gives its quotient isomorphism. I did not replace this with the etale-only restriction nodes.

Step 1 uses the definition of groupoid schemes only for the explicit unique-endpoint construction. The affine-square-monomorphism statement really supplies absolute separatedness of R, and the cancellation statement's clause (b) really supplies separatedness of each projection. No separatedness of S or quasi-compactness of R is inferred or assumed.

Step 2 uses the first new node for each actual pointed chart and finite open subgroupoid. The existing open-image statement is valid for algebraic spaces and specializes to scheme maps, so the chart images are open. The affine-qcqs statement supplies quasi-compactness, and the compactness definition supplies an actual finite subcover of these same charts. Refining arbitrarily could lose a chosen finite subrelation; the proof does not do that.

Step 3 checks the hypotheses of division one by one. Restriction along g_i keeps relation monicity by the displayed fibre-product formula. The quasi-finite definition includes local finite type. The monomorphism-with-finite-type-composite statement, applied to the relation map followed by a projection, supplies separatedness and local quasi-finiteness of that map. Division's statement supplies the affine quotient, the surjective finite locally free object map, the restriction isomorphism, and the cartesian unit square; none is borrowed only from its proof.

Step 4 uses finite locally free only for flatness and local finite presentation, and the given surjectivity makes q an fppf cover. Site base-change axioms give the source cover A -> B. The existing representable-fppf-descent statement explicitly includes locality on both source and target for flatness and local finite presentation, exactly as used for the two projections. It supplies no source descent for etaleness, which the proof does not need.

Step 5 uses division's explicit cartesian unit square. The map A -> R-bar factors into two base changes of q, hence is a covering by site axioms. The same existing descent statement explicitly tests open immersions after a target fppf covering. Thus openness of P -> A really implies openness of the unit, rather than just an open point image.

Step 6 uses precisely the existing open-unit lemma's flat, locally finitely presented and open-unit hypotheses. The second new node then reflects monicity from the original restricted relation and gives the required isomorphism of fppf quotient sheaves. Step 7 uses the actual universe/skeleton convention, with bounded constructions in both new inputs and finite choices, not a new size axiom.

Checked the B--E failure types against the files and source: each new statement introduces all its objects and notions, has only a statement and no hidden proof, and is neither elementary nor a restatement of an item clause. Every non-elementary item step cites the exact input used; citations.json contains full verbatim statements for all step/node pairs. All steps are under 2000 characters. Off-unit generic tools are declared in split_report.tool_uses. No SGA source is used. The empty affine scheme admits the empty finite covering. The diagonal relation admits P equal to its unit; for a nonreduced finite flat relation the quotient map q may fail to be etale, which is why the generic fppf restriction lemma is necessary. No reducedness, Noetherian hypothesis, field base or constant positive rank is introduced. With q the identity the restriction lemma is the identity comparison; over the empty object scheme both sides are empty sheaves. Its covering hypothesis is essential (an empty map to a nonempty scheme would not preserve the quotient). No correction of the item's statement was needed.
