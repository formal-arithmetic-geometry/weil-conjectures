# Stage-1 report: lem-pe-comparison-etale-slice-abelian-pullback

Group Q20, 2026-10-21. Direct delivery; no second worker was started.

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-comparison-etale-slice-abelian-pullback.json`: statement item, now split in four steps; statement and statement dependencies unchanged. Mathlib verdict: no exact match or one-line specialization for the entire item.
- `citations.json`: eight verbatim statement excerpts, one for each citation in the four proof steps.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. No unit file, Lean file, repository file, launcher file, or compiler artifact was written.

## Attachments

None for this item. I searched the project source for the exact blueprint tag and for comparison pullback, slice and localization restriction. Existing partial implementations include `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction` (Etale/LowerShriek/OpenImmersion/Defs.lean:181), `AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction` (ProEtale/FiniteCoefficient/LowerShriek/Open/Defs.lean:193), and `AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso` (ProEtale/Comparison/LowerStarAcyclic.lean:164). The étale site equivalence is `AlgebraicGeometry.Scheme.Etale.overEquiv` in Mathlib/AlgebraicGeometry/Sites/EtaleOver.lean:66. These are project declarations, not Mathlib declarations despite the directory name of the last one. Their individual signatures do not state the whole item, in particular both localized-site identifications together with the specified restricted comparison. I therefore do not submit an ATTACH claim. The DAG already has nodes for the general facts needed here; no duplicate attachment/node was introduced. The file LowerStarAcyclic.lean also contains an unrelated sorry (line 121); its mere presence as a source is not treated as evidence of a finished item.

## WANTED

None. All mathematical sources used are present in the read clone.

## Findings and corrections

The original item had no proof or proof dependencies. The statement is correct and is preserved exactly. I supplied the explicit equivalence for the étale slice, reused the existing weakly étale site equivalence and abelian restriction lemmas, then wrote the actual three-factor composite with the comparison square. This avoids moving a clause of the item to a new node.

The current blueprint is main-20261015, sec-proetale-coefficients/sk-prop-sf-comparison. I read its section and proof: the first paragraph uses injective acyclicity to prove the derived unit. The parent lem-pe-comparison-injective-left-modules-acyclic needs exactly this item's two slice identifications and abelian pullback compatibility in its steps 2 and 3. The stored unit record still has the older master statement and no proof steps; I did not change its route or realization fields, since this item is not its key node. I refined blueprint.from.place to name the current paragraph and the parent localization input, preserving the ancestor and via chain. Whole-blueprint searches for `03CE`, `comparison etale slice`, `inverse image restriction`, `étale slice`, and `localized sites` found no blueprint statement of the entire item. Existing related DAG nodes were read and reused.

The only issue found in a search tool was display of single-file grep hits: the query `comparison|[Ll]ocalization|[Oo]ver` with subpath AlgebraicGeometry/Sites/Proetale.lean returned line numbers in the file column. I preserved this result as returned and read the actual source directly, then ran a directory grep that produced ordinary file-and-line hits. This did not block the search or delivery and no tool was changed.

## Not duplicates

No new nodes were created. In particular, the general pro-étale restriction clause is already lem-sfb-proetale-object-inverse-image-restriction, its site equivalence is lem-weil-proetale-weakly-etale-localization, the étale restriction is lem-weil-pbc-etale-inverse-image-restriction, and the canonical square is lem-weil-pbc-comparison-pullback. These are reused rather than restated as new nodes.

## Review by Q20

I read Stacks Sites Tag 00Y0 (definition-localize and the immediately following formula for restriction), the whole statement and proof of Tag 03CE (lemma-localize-given-products), Morphisms Tags 02GN and 02GW (étale composition and cancellation), the paragraph on restriction in Etale Cohomology Tag 03S2, and Pro-étale Tag 09A5 (section-morphism), including the displayed square and its inverse-image equality. For the pro-étale site equivalence I also checked More on Morphisms Tag 0951 (lemma-weakly-etale-permanence). There are no new-node sources to review. The proof origin is marked agent because the final four-step assembly is mine, although all ingredients have existing nodes and sources.

Step 1 uses exactly the statements of lem-weil-pbc-etale-composition-cancellation, def-weil-pbc-etale-site and def-pur-localized-ringed-site. The first supplies both implications required to construct the mutually inverse object operations; the latter two state the covering families and restriction formula. This step is elementary from those statements: no geometric permanence theorem is silently reproved, and the equivalence leaves underlying objects and arrows unchanged. The coverings agree because they are the same jointly surjective étale arrows. No separation or quasi-compactness is used.

Step 2 uses the inclusion asserted in def-weil-pbc-site-comparison-morphism to regard the given étale v as a small pro-étale object, then precisely clause (1) of lem-weil-proetale-weakly-etale-localization, which states the equivalence, its object/arrow description, and equality of coverings. The auxiliary ring in that node may be chosen to be Z; neither its coefficient nor module clauses are used. The universe bounds are inherited from the item's common larger universe, with compatible skeletons; no large colimit is taken.

Step 3 uses clause (1) of lem-weil-pbc-etale-inverse-image-restriction and the abelian part of clause (1) of lem-sfb-proetale-object-inverse-image-restriction. I opened both statements and verified that they identify the actual scheme-induced inverse images, supply the section formulas, and assert naturality in the sheaf. The first requires an étale scheme morphism, as given; the second requires a site object, supplied in step 2. I use neither the finite-ring interfaces nor the module pullback clauses. In particular, the item remains about every abelian sheaf. The pro-étale lemma requires no monomorphism.

Step 4 uses the displayed inverse-image isomorphism of lem-weil-pbc-comparison-pullback, with its source and target exactly as quoted in citations.json. Its abelian interpretation is also explicit in that node's existing realization and proof; I do not use an identification of different coefficient categories. Substituting u=v, U=W, V=X gives c in the direction written. Starting from the restricted comparison pullback, the inverse of rho_p goes to v_proet inverse-image of nu_X inverse-image F, c inverse goes to nu_W inverse-image of v_et inverse-image F, and nu_W inverse-image of rho_e reaches the required target. Thus every arrow is typed and invertible. Natural transformations composed and inverted remain natural, so the component composite gives a natural isomorphism. There is no invocation of proper base change or direct-image comparison (which would add qcqs hypotheses).

For delivery-errors B1-B10 I verified the unchanged self-contained statement, all existing definition references, JSON/TeX encoding, the literal source tags, genuine search provenance, blueprint location, and the lack of a full project attachment. The old five Mathlib search records already in the repository node are retained; seven new searches were actually run with msearch.py and their exact tool/query strings are appended, with the returned hits and verdicts. I read Over.lean:248-290, Sites/Equivalence.lean, and Sites/Proetale.lean:140-200. Generic overPullback and sheafCongr do not state this small-site comparison square. Two different semantic phrasings were tried. No service was unavailable in these new searches.

For C1-C8 I checked every uses entry against its node statement and supplied literal excerpts, including the clause that explicitly mentions abelian groups in the pro-étale restriction lemma. The proof uses statements, not a construction hidden in a dependency's proof. The generic off-unit tools are declared in split_report.tool_uses with their limited roles; they do not replace the unit comparison/acyclicity route. I checked the transitive dependency closure of every proposed statement dependency used as a tool and none reaches this item. proof_deps is exactly the union of step uses.

For D1-D5 there is no new node and no relocation of the whole argument to a restated clause: step 1 gives the inverse site operations and step 4 gives the complete comparison composite. The reused broader localization and pullback statements already existed independently. Every step is under 900 characters, so there is no non-elementary step over the 2000-character threshold or hidden long comparison argument.

For E1-E7 I checked W empty, W=X with the identity map, a proper open étale object, a disconnected étale object, and a finite étale cover of degree greater than one. In the identity case all functors reduce to the same restrictions and the comparison is the identity under canonical identifications. For the empty scheme all asserted categories and restriction operations remain defined. The degree-greater-than-one case is important: v need not be a monomorphism, but neither restriction lemma requires this. Zero sheaves and arbitrary abelian groups require no torsion or finite coefficients. All fibre products belong only to the cited general lemmas; no accidental affineness or qcqs assumption enters the proof. There is no statement dispute, source error or hypothesis correction.

## Unfinished work

None in the mathematical split. The server dry run and push are the remaining delivery operations.
