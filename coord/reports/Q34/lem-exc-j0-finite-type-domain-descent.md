# Q34: lem-exc-j0-finite-type-domain-descent

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-j0-finite-type-domain-descent.json`: statement node, now split; no Mathlib match. Its statement and statement dependencies are unchanged. Seven argument steps reuse existing nodes, with proof dependencies exactly their citation union.
- `citations.json`: a verbatim statement quotation for every citation in every proof step.
- `report.md`: this report. `searches.jsonl` is written by the authorized search command; `write_split.py` is sandbox-local preparation code.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. In particular, a nonzero free algebra being faithfully flat is proved by the explicit basis/tensor calculation inside step 5, not turned into a new node. No item clause has been moved to another node.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact item id and blueprint tag and for J-0, JZero, regular-locus and regular-descent terminology. No declaration states this item. The inherited item has no Lean declaration to audit; reference master sorries are not treated as completed proofs.

## WANTED

WANTED: `literature/stacks-project/more-algebra.tex`, Tags 07PA (lemma-J-0-goes-down) and 07P7 (definition-J), for lem-exc-j0-finite-type-domain-descent.

WANTED: `literature/stacks-project/algebra.tex`, Tags 051R (algebra-lemma-generic-flatness-Noetherian), 07NG (lemma-descent-regular), 00FN (Noetherian permanence), 00E0 and 00E4 (basic opens), 00OD (regular ring), 00HB (faithfully flat), for lem-exc-j0-finite-type-domain-descent.

The checkout contains citation lists but no Stacks source tree or blueprint texts. I did not download a document or write outside the sandbox. I read the source online at https://stacks.math.columbia.edu/tag/07PA, https://stacks.math.columbia.edu/tag/07P7, https://stacks.math.columbia.edu/tag/051R and https://stacks.math.columbia.edu/tag/07NG. In accordance with the missing-local-literature rule, `proof_origin.by` is `agent`; its argument follows the cited route and supplies the elementary details below. No new node requires its own source review.

## Findings and route

No statement dispute: the item is exactly the domain J-0 descent assertion of 07PA after expanding J-0 via 07P7. The Noetherianity of S implicit in J-0 follows from finite type over the Noetherian R, so there is no missing hypothesis. I retain the item statement verbatim.

Read the chapter record `sec-smooth-purity` and unit `sk-prop-a1-kummer`, the three-level rule of SETUP, GOAL, coord/dag-sync.md, and the ancestor record `thm-exc-curve-open-dimension-general`. The item is a generic algebra input to the ancestor's field-excellence argument, along its existing J-2 criterion branch; it does not change the chapter or unit statement, or the unit's proof route. The original unsplit item had no proof to repair. Its precise `blueprint.from.place` is retained; `same_as` is [] after whole-blueprint searches for J-0 and regular locus. The ancestor command confirms the ancestor remains thm-exc-curve-open-dimension-general. No unit binding or realization fields are changed.

DAG searches by tag and concept found `lem-pur-noetherian-algebra-module-generic-freeness` for 051R, `lem-weil-pbc-regular-ring-faithfully-flat-descent` for 07NG, and the existing basic-open, Noetherian permanence and regular-localization nodes. I opened their statements rather than relying on titles or their proofs. The generic freeness, localization permanence and regular descent lemmas from other units are declared as tool requests only in `split_report.tool_uses`; the maintainer can judge them. They are generic tools below the existing route, not replacements for a unit step. No maintainer-owned `tool_uses` field is set.

## Mathlib searches

All new searches were run with `/home/ubuntu/weil-launcher-nt/msearch.py Q34 lem-exc-j0-finite-type-domain-descent ...` and are appended to the item with their actual tool, query and logged results. I inspected all returned types/lines. The two LeanFinder phrasings concern nonempty regular-open descent and J-0 under a dominant finite-type map, respectively. Their hits are about finite generation, regular sequences, Noetherianity, normalization or proper maps to fields; they do not state this assertion. Loogle `IsRegularRing, IsOpen` returned no hits. Grep `JZero|J-0|regularLocus|regular_locus` returned graded-ring `projZeroRingHom` lines, not regular-open descent. LeanSearch returned Internal Server Error and is recorded as unavailable. The item's earlier search history is preserved. No new node needs a search or duplicate-tag justification.

## Not duplicates

There are no new/existing node pairs: no new nodes were created. The existing 051R and 07NG nodes were reused, as were the existing localization and spectrum nodes.

## Review by Q34

I read 07PA itself, not just its title: it first restricts S to a regular principal open, then shrinks the base by generic flatness, then applies faithfully flat descent. I also read 07P7 to compare the expanded statement with J-0, 051R to check its exact algebra/module hypotheses and its possibly infinite free rank, and 07NG to verify that regularity of the target includes Noetherianity. The local literature files are absent, which is why I explicitly use agent proof origin and the WANTED entries. Sections B through E of delivery-errors were checked against the seven steps, with the cited node statements open.

Step 1 takes the basic-open basis from `lem-weil-pbc-spec-localization-away-basic-open`, the fraction criterion from `def-weil-ring-localization-away`, and finite generation from `def-weil-pbc-finite-type-algebra`. Their statements actually provide these facts. Choosing a point in the given nonempty V makes the chosen g nonzero. I spell out the extra algebra generator g inverse and use the domain hypothesis to keep R injective in B; neither finite type of a localization nor injectivity is silently assumed.

Step 2 uses `lem-weil-pbc-finite-type-algebra-noetherian` only for its explicit finite-type permanence assertion; step 1 verified its finite-type hypothesis and the original R is Noetherian. The basic-open node identifies the contracted prime in D(g). It does not assert a local-ring isomorphism, so the proof gives both fraction formulas for B_P and S_q, their denominator checks, and the inverse calculation using the two localization definitions. `def-weil-regular-scheme` then supplies exactly the definition of a regular ring, after Noetherianity has been established. Regularity transfers across this explicit ring isomorphism because both the maximal ideal and its generating sets, and the prime chains defining dimension, correspond under the isomorphism. There is no invocation of a theorem about normality or excellence at this point.

Step 3 takes only the statement of `lem-pur-noetherian-algebra-module-generic-freeness`: use the original Noetherian domain R, the finite-type B of step 1, and M=B generated by 1. Its conclusion gives free localized M over R_a, with a nonzero in R. The displayed fraction description identifies the localized module with the ring B_a and its natural R_a-action. It does not give finite rank, so the proof never assumes finite rank.

Step 4 takes regularity of B_a from the full statement of `lem-weil-pbc-localization-of-regular-ring`, with multiplicative subset the powers of the image of a. Its input B is regular by step 2. The localization definition proves B_a is nonzero, using that a stays nonzero in the domain B. The free-module definition then forces its basis set to be nonempty. This is the point where the domain and injectivity hypotheses prevent generic freeness from yielding the zero algebra with empty basis.

Step 5 cites just the free-module, tensor-product and faithfully-flat definitions and writes the construction itself: coefficient maps identify T tensor N with finitely supported N-families, with the explicit inverse sum of pure tensors. Bilinearity gives the inverse identities and naturality; exactness is preserved by lifting finitely many coordinates and reflected by inclusion and projection at one fixed basis index. This is an elementary calculation, not a hidden appeal to flatness from a definition. It proves the full exact-complex criterion of the cited faithfully-flat definition. No finite-dimensionality, finite presentation, tensor-colimit theorem or spectral sequence is smuggled into the calculation.

Step 6 invokes `lem-weil-pbc-regular-ring-faithfully-flat-descent` for exactly what its statement says. Step 5 proves the map is faithfully flat and step 4 proves its target is regular. The resulting regularity is that of R_a, not yet that of all R. The proof deliberately concludes only on the required open.

Step 7 uses openness and the prime correspondence from the basic-open node. The domain zero prime and nonzero a make D(a) nonempty without a further generic-image lemma. As in step 2, the prime-localization definitions and explicit inverse fraction maps identify the relevant local rings; regularity of R_a then gives regularity of R_p for every p in D(a). Every node quotation in citations.json is copied verbatim from the corresponding statement; none quotes a proof or attributes the local-ring calculation to the topological correspondence node.

For small cases I checked R a field (the base spectrum is a single regular point), the identity R=S (the given regular open already suffices), and S=R[1/h] with h nonzero (the final open can shrink inside D(h)). As a singular example, k[t^2,t^3] injecting into k[t] does not imply the base is everywhere regular; the conclusion is correctly restricted to a nonempty open away from the cusp. Taking an empty free basis would invalidate faithful flatness, but step 4 rules that out. Taking S=0, a nilpotent g, or a noninjective base map is excluded by the stated domain/injectivity hypotheses. Infinite free bases are allowed: all tensor-coordinate families and coordinate lifts remain finitely supported. These checks required no statement correction. The detail added to the source's compressed proof is the base shrinking and its faithfulness check, not a new stronger conclusion.

## Unfinished work

No unresolved mathematical issue at this level. The existing non-Mathlib dependencies remain their own items. The requested output is a stage-1 split, with no Lean changes or compiles. Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q34 lem-exc-j0-finite-type-domain-descent --no-push`. Its final output is retained in sandbox `dryrun.log`; the final READY response is conditional on its OK result. Delivery/push is reserved for the second reader.

## Second reading by Q34

Step 1 checked against Stacks Tags 07PA, 00E0, 00E4 and the cited localization, finite-type, and spectrum statements; verdict: correct, with injectivity and nonzero localization hypotheses explicitly justified.
Step 2 checked against Tags 07PA, 00FN, 00OD and every cited node statement; verdict: correct, including the explicit inverse local-ring maps and regular-local invariance.
Step 3 checked against Tag 051R and the generic-freeness node; verdict: correct, with the module localization identified with the localized algebra and no finite-rank assumption.
Step 4 checked against Tags 07PA, 00OD and the localization/free-module definitions; verdict: correct, including nonvanishing and the nonempty basis argument.
Step 5 checked against Tag 00HB and the free-module and tensor-product definitions; verdict: correct elementary coordinate proof of faithful flatness for an arbitrary nonempty basis, including infinite bases.
Step 6 checked against Tag 07NG and the faithfully-flat descent node; verdict: correct, with exactly the stated hypotheses supplied by Steps 4–5.
Step 7 checked against Tags 07PA and 07P7 and the basic-open/localization statements; verdict: correct, including nonemptiness of $D(a)$ from the domain's zero prime and the explicit local-ring correspondence.
New nodes: none; therefore there were no node statements, Mathlib leaves, duplicate nodes, or node searches to repair. Existing dependencies were checked by tag and by their verbatim quotations in `citations.json`.

Changes made: none. The first reader's statement, seven proof steps, citations, source metadata, blueprint metadata, and search log all passed the B1–B7 and C1–E5 checks. The required dry run was rerun and passed preflight.
