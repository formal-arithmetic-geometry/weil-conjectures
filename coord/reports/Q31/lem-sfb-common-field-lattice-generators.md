# Q31 stage-1 delivery: lem-sfb-common-field-lattice-generators

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-common-field-lattice-generators.json: statement split into five steps; not a Mathlib leaf.
- citations.json: six verbatim statement excerpts, covering every proof-step citation.
- report.md and searches.jsonl: this report and the search command's actual log.

New nodes: 0. New Mathlib leaves: 0. The original statement is unchanged. All changes are inside this sandbox.

## Attachments

None. Searched the live lean/WeilConjectures library for the item tag, lattice/generator notions, common fields and composita. The hits concern field-theory composita and the condensed coefficient ring, not the full two-generator statement. In particular a common-extension-field theorem does not prove the pro-etale derived-module comparison. No attachment is claimed on the strength of a sorry declaration or a partial match.

## WANTED

None: the blueprint source and the source passages needed for this split are available locally.

## Problems corrected

The item had no proof. Its statement dependency list included the integral-generators theorem and scalar-six comparison theorem even though these are used to prove the assertion, rather than define its objects. Moved them to proof dependencies. Added the existing lisse-module notion and the precise locally closed extension-by-zero convention to statement dependencies. No mathematical change to the statement, no route departure, and no source dispute was necessary.

The phrase "scalar transitivity and scalar/extension-by-zero comparison" now has a specified composite and its direction, rather than standing in for an argument. In particular it first identifies the F-valued scalar extension with K, then applies Qlbar scalar extension to the inverse identification, then uses tower transitivity.

## Mathlib and duplicate search

Read the existing item and retained its original Q14 searches. Ran the Q31 logged searches with leanfinder, loogle, grep and leansearch, and a second semantic phrasing targeting locally free sheaves. Read every returned hit. The finite-dimensional supremum instance is indeed at Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:78, but this is only the field part. ModuleCat.extendScalarsComp at Algebra/Category/ModuleCat/ChangeOfRings.lean:984 is ordinary scalar transitivity, not the full derived sheaf result. The second semantic query returned SheafOfModules.mapFree and mapFreeIso; read Algebra/Category/ModuleCat/Sheaf/Free.lean:180-215 and the logged grep at lines 184 and 198. These give a free-sheaf comparison for a coproduct-preserving functor with a unit comparison. They do not give all the local, derived and immersion identifications in the item. The CategoryTheory-only grep returned zero hits; recorded it as such, and then searched the actual Algebra/Category/ModuleCat/Sheaf directory. All recorded Q31 queries are literal queries that ran; no service was unavailable.

Searched the entire DAG and the blueprint index for compositum and lattice, and inspected the scalar, lisse and generator nodes. blueprint_refs.py ancestor gives det-thm-sfb-proper-base-change-rational. Existing det-def-sfb-qlbar-condensed-subextensions states the common finite field fact. Existing lem-sfb-locally-free-derived-scalars states both local freeness after base change and its degree-zero derived comparison. Existing det-lem-integral-models-generators (3) supplies integral constructibility. Existing det-prop-scalar-six-pullback (2),(3) supplies the two final comparisons. Therefore none of these facts is duplicated in a new node. The item has no blueprint duplicate stating its full conclusion; same_as remains empty.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by Q31

I read the chapter and proper-base-change unit, in particular its rational-coefficient step, and paragraph (3) of the current det-thm-sfb-proper-base-change-rational.proof.md. The unit's route rationalizes integral comparisons and then performs devissage in each variable. A pair of lattice generators must first be placed over a single integral coefficient field. This split supplies exactly that preliminary identification; it does not replace the integral argument or the devissage.

For step 1 I read the statement and source file of det-def-sfb-qlbar-condensed-subextensions, clause (1). It asserts finiteness and containment for every finite family, including the pair at hand. Thus F is the actual compositum inside the fixed closure. Its source is the main-20261015 blueprint file in sec-proetale-coefficients/sk-def-sfb-qlbar-condensed. This is a generic field-theory tool, declared in split_report.tool_uses; no new common-field lemma is needed.

For step 2 I read def-weil-l-adic-coefficient-extension and sk-def-sfb-coefficient-change. The first gives the valuation-ring formula and uniqueness of the extended absolute value; the fields here have the induced absolute value from the same fixed closure. Hence inclusions preserve the valuation rings and are continuous for their subspace topologies. Postcomposition on continuous-function sections gives the coefficient maps, and their composites agree section by section. The second cited node explicitly says that coefficient change is functorial in the ring map, which is exactly what the step uses. This is an elementary restriction-of-functions argument, not an unsupported flatness claim.

For step 3 I read the whole statement of lem-sfb-locally-free-derived-scalars. Its hypothesis is local finite freeness over a ring sheaf on a small site; the project's usual small pro-etale site and its slice covers meet it. A cover of the terminal object pulls back to one over every object. Its conclusion gives both local finite freeness of B tensor L and the canonical derived-to-ordinary comparison. I also read the local tensor-pullback statement in Stacks sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback, and the flatness passage Tag 0GN1, lemma-flatness-sheafification-refined, which are sources of this existing lemma. The split cites the lemma's statement rather than reproducing or assuming its internal proof. Neither flatness of the coefficient algebra nor exactness on arbitrary modules is assumed.

For step 4 I read clause (3) of det-lem-integral-models-generators and its current blueprint statement/proof files under sk-lem-integral-models. It says a_!L_0 lies in Dbc for a locally closed immersion and lisse finite free integral lattice. Substitute F, W_i, a_i and L_{i,F}; F is finite by step 1, W_i is standing by hypothesis, and local freeness was proved in step 3. Its generator and finite-cone-generation clauses are not used. This avoids hiding constructibility behind a definition or creating a node for a clause already stated.

For step 5 I read the full current DAG statement of det-prop-scalar-six-pullback and its blueprint source. Clause (2) explicitly covers locally closed immersions in the standing separated finite-type setting, exact extension by zero on unbounded complexes, and ordinary derived tensors without completion. Clause (3) supplies scalar-tower transitivity compatibly with (2). Both needed clauses appear in the citation excerpt. Applying (2) to L_i[0], then the comparison from step 3, gives the intermediate F-valued identification; applying Qlbar extension to its inverse and then (3) gives the displayed isomorphism in the requested direction. Step 2 identifies the composite coefficient map with the original one. Naturality is part of the cited statements, so no unproved matrix calculation or arbitrary choice of basis is used to call the final map canonical. This scalar-six node is declared as a generic comparison tool in split_report.tool_uses.

I checked the cases E_1=E_2, one E_i contained in the other, and both equal Q_l: the compositum still has the stated inclusions, with identity scalar maps where appropriate. Rank zero, empty strata and empty ambient schemes give zero modules and the same comparison; varying finite ranks are allowed by the local-freeness lemma. The two strata may belong to different schemes; their covers are never compared. No ramification or flatness hypothesis on O_F over O_E is needed for the local-free derived calculation. The small-site convention is the same one used by the cited module-sheaf lemma. All proof steps are under 2000 characters and hide no new sublemma.

I checked that every cited node exists and none reaches this item, so the new proof edges do not create a cycle. citations.json quotes are exact substrings of their current node statements. The split uses no SGA source, writes no Lean, and runs no compiler or local DAG/preflight checker.

## Unfinished work

None for this one-level split. The existing dependencies retain their own stage states. The required server dry run and push are performed after this report is written.
