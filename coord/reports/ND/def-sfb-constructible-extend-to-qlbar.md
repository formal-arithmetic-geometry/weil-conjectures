# Stage 1 report: def-sfb-constructible-extend-to-qlbar

1. Files written: `dag/nodes/sec-six-functors-basics/def-sfb-constructible-extend-to-qlbar.json` — existing definition, split; no new nodes and no Mathlib leaves. Also refreshed `citations.json` (empty, since there are no proof steps) and this report. `searches.jsonl` is the search command's actual log.
2. Attachments: none. The slopmaster2 project search for the exact id, `constructibleToPadicAlgCl`, and the coefficient-category names found no exact declaration. Upstream master is reference material only.
3. WANTED: none.
4. The returned version had the correct restriction definition, but its citation of `def-sfb-dcons-subfield` had not been revalidated after that dependency's statement changed. The current dependency explicitly defines the condensed ring of the topological subfield E, pulls it back to E_X, specifies module objects, and states that morphisms are ambient. The item now spells out the restricted functor's action on objects and morphisms against those current categories. No hypothesis or mathematical meaning changed.
5. The repair is complete subject to the required fresh second reading; no Lean work or compilation is part of this stage.

## Repair of returned delivery

Return L: “cited node def-sfb-dcons-subfield: statement changed since the reviewed delivery; rebase and revalidate the citation”. I compared the retained returned sandbox with the current shared item: the original statement and four dependencies agree verbatim. I rebuilt the item's sandbox record from the current shared record, retained the split, and added the explicit object/morphism description and current review metadata. The delivery command rebuilds its temporary delivery commit on current `origin/newtargets-dag`, so the dry run revalidates against that base rather than merely retrying the returned commit. Nothing is pushed by this worker.

I reread all four current dependency statements, not just the named changed dependency, and the exact blueprint files at orders 1759, 1762, 1763, 1765 and 1767. In the current `def-sfb-dcons-subfield`, the source objects are bounded complexes with constructible cohomology in D(Mod_{E_X}); E_X is p_X^* of the condensed ring of E with the subspace topology. This is exactly the domain of `def-sfb-derived-extend-to-qlbar`. Its codomain is D(Mod_{Qbar_{ell,X}}), and `def-sfb-dcons-qlbar` selects the bounded constructible full subcategory in that codomain. The statement of `lem-sfb-extend-to-qlbar-constructible` takes any bounded constructible E_X-complex under the same prime, scheme and finite-field hypotheses and concludes bounded constructibility over Qbar_{ell,X}. Thus the changed source-category definition remains a valid citation. No additional assumption on X, coefficient completeness condition, or coefficient-category comparison is used.

## Review by ND

I read the unit `sk-thm-sfb-qlbar-two-colimit` and chapter `sec-six-functors-basics`, the current blueprint definition and the unit proof paragraph “The cocone itself”. This definition realizes that paragraph's restriction clause, and does not replace any of the unit's descent arguments. It is not the unit's key theorem, so the unit's `realized` fields are untouched. I also read master `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:105-196`: its full-subcategory lift applies the ambient derived extension and the named preservation lemma. That preservation lemma has `sorry` there; master is not an attachment or evidence that the preservation theorem is finished. I do not claim equivalence between the blueprint's constructibility notion and any different upstream implementation; the item consistently uses the categories of its current four cited DAG statements.

For C3/C4, the category citations say exactly what this definition needs. `def-sfb-dcons-subfield` ends with “Its morphisms are those in $D(\Mod_{E_X})$.” `def-sfb-dcons-qlbar` says it is “the full subcategory” of the target ambient derived category. `def-sfb-derived-extend-to-qlbar` explicitly has source D(Mod_{E_X}) and target D(Mod_{Qbar_{ell,X}}). `lem-sfb-extend-to-qlbar-constructible` states the target bounded-constructibility property, rather than merely defining it. Consequently an input object is sent to an admissible output object, and every morphism has exactly the required source and target in the full subcategory. Identities and composites are those of the ambient functor. This is the elementary unpacking of restriction of a functor, not a hidden extension-of-scalars theorem. This is a definition: `proof` and `proof_deps` remain empty and no step quotations are required in `citations.json`.

For B/D and C1/C5, no new node is needed: all four notions and the preservation theorem already exist. I searched the full DAG for the item id, `constructibleToPadicAlgCl` and its scalar-extension notation, and used `tools/blueprint_refs.py search` for `constructibleToPadicAlgCl` and `bounded constructible complexes`. The nearby finite-subfield restriction has target D_cons(X,F), the integral-to-rational restriction has source O_E coefficients, and the composition-isomorphism node adds a transitivity assertion: none duplicates this E-to-Qbar definition. Mathlib searches were run through `msearch.py` (LeanFinder twice with different phrasings, Loogle, LeanSearch and grep); the recorded queries are copied from `searches.jsonl`. The semantic hits describe ordinary restriction of scalars, condensed-module categories, or ambient derived functors. I read the candidate source files; none is this definition for the cited bounded constructible coefficient categories. No new-node source/tag or duplicate-pair requirement arises.

For E, the source and target coefficient rings are the same pulled-back condensed rings used by the ambient functor, and the preservation lemma assumes exactly a prime ell, a scheme X, a finite E inside Qbar, and an input bounded constructible complex. This definition asserts no triangulated closure or exactness, so it does not need the extra hypotheses of those properties. I checked the empty scheme, the zero complex, E = Q_l, and a field-valued point; each is allowed and the object/morphism restriction remains meaningful. No finite-field or characteristic restriction was smuggled into this definition. The repair corrects the missing citation revalidation by explicitly checking both ambient categories and recording the actual restriction; it introduces neither a restatement lemma nor an unsplit proof obligation.

## Dependency statements revalidated

SHA-256 of the exact current statement text, to identify what this repair read:

- `def-sfb-dcons-subfield`: `c533e6c8f71ed75b388fd0099ba8b8a74eb980610c387fdb30b1d9ef2ac5298e`.
- `def-sfb-dcons-qlbar`: `a9844cd54f18ffe97beae9bb5271ab4b3d89af01361b09c7fcc4d718e60b1a64`.
- `def-sfb-derived-extend-to-qlbar`: `cc06af4ad50ce6c312a382620e1db42c85deb530e742140aa8e950bc19d3d602`.
- `lem-sfb-extend-to-qlbar-constructible`: `5a6465a405b3782003b835ba414fc9117c590948ad2a588c70205101d91c10ba`.

## Earlier second reading by ND (before this return)

The following is the earlier reader's review of the returned version. It predates this repair and does not certify the repaired version; a fresh reader must review the new object/morphism description and current dependency statements.


- Item statement: checked against the displayed blueprint node and upstream master `TwoColimit.lean`, lines 189–196 (the `constructibleToPadicAlgCl` definition); the prime `ell`, arbitrary scheme `X`, finite extension `E` inside `Qlb`, source and target bounded constructible categories, ambient derived extension, and constructibility-preservation condition agree hypothesis by hypothesis.
- Proof steps: none; this is a definition node, so `proof`, `proof_deps`, and `citations.json` are correctly empty.
- New nodes: none; the four dependencies already exist, so B1–B7, duplicate checks, and new-node Mathlib leaves are vacuous.
- Dependency statements: reread `def-sfb-dcons-subfield`, `def-sfb-dcons-qlbar`, `def-sfb-derived-extend-to-qlbar`, and `lem-sfb-extend-to-qlbar-constructible`; each supplies exactly the category, ambient functor, or preservation fact used by the definition.
- Edge cases: checked the zero object, a field-valued point (ordinary scalar extension), the empty scheme (trivial source and target), and the base case `E = Q_l`; all are included by the stated hypotheses and the restriction remains defined.
- Existing-node and project search: searched the DAG and blueprint for the id and `constructibleToPadicAlgCl`, and searched slopmaster2 for the declaration and key terms; no duplicate node or sorry-free declaration was found.
- Changes: no node or citation changes were needed; this second-reading report is the only modification.

## Second reading by ND

- Item statement: checked the exact main-20261015 blueprint node `def-sfb-constructible-extend-to-qlbar` (order 1767) clause by clause; the prime, scheme, finite intermediate field, source and target full subcategories, ambient derived extension, and constructibility-preservation condition agree, and the added object/morphism sentences only unpack “restriction”.
- Proof steps: none; this is a definition node, so there are no proof dependencies or citation quotes to verify.
- New nodes: none; B1–B7 and duplicate-node checks are vacuous, and the four cited facts are existing dependency nodes.
- Dependency statements: reread `def-sfb-dcons-subfield`, `def-sfb-dcons-qlbar`, `def-sfb-derived-extend-to-qlbar`, and `lem-sfb-extend-to-qlbar-constructible`; each states exactly the category, ambient functor, or preservation property used by the restriction.
- Blueprint and searches: checked the definition source and unit “The cocone itself” paragraph; the recorded LeanFinder, LeanSearch, Loogle, and grep searches ran through `msearch.py` and found no Mathlib declaration of this project-specific functor.
- Edge cases: checked the zero complex, empty scheme, field-valued point, and $E=\mathbf Q_\ell$; all satisfy the hypotheses and the full-subcategory restriction remains defined.
- Changes: none required after this reading; the repaired object/morphism clarification and current dependency revalidation are retained.
