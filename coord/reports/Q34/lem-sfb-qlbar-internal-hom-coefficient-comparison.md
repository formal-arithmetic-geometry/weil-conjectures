# Q34 stage-1 report

Item: lem-sfb-qlbar-internal-hom-coefficient-comparison.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qlbar-internal-hom-coefficient-comparison.json: existing statement split into five steps; no Mathlib match.
- citations.json: twelve step/node entries, each quoting the actual existing statement verbatim.
- report.md: this report. searches.jsonl is the unmodified msearch.py output; write_split.py is a sandbox-only preparation script.

No new nodes, no new Mathlib leaves. No unit or chapter record changed. The statement is unchanged. The unused sk-def-sfb-bounded-constructible statement dependency was removed: the item explicitly does not assume constructibility.

## Attachments

None. Searches for the exact blueprint tag and for algebraic-closure/internal-Hom coefficient comparisons in lean/WeilConjectures found no declaration proving all these clauses. The ambient derivedHom definition is not a coefficient comparison. isMonoidalClosed_boundedConstructible at SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:485 has a sorry at line 488 and states constructible closure, not this item. The existing generic comparison lives under Sheaf.Paper, so it is cited as a DAG node rather than offered as an upstream attachment.

## WANTED

None.

## Audit findings and changes

The imported item needs no mathematical statement correction. Its explicit continuity hypothesis makes it a specialization of the existing lem-sfb-dc-hom-filtered-colimit, whose statement includes the evaluation normalization, exact termwise-colimit interpretation, three-arrow formula, naturality and independence from bases. Creating a second generic comparison node or separate nodes for the formula's clauses would be duplicate work. The split instead verifies the hypotheses for the actual coefficient diagram.

The source is read as motivation, not as a verbatim theorem in this generality. Bhatt–Scholze Lemma 6.8.2(2), printed pp. 58–59, supplies the coefficient-union context; Proposition 6.8.14 and Remark 6.8.15, printed pp. 61–62, concern constructible coefficient passage and ambient operations. The item and its general comparison lemma already explicitly label the conditional generalization as an agent formulation. I retain that distinction in proof_origin. No SGA source is used.

The inherited blueprint.from.node is null. The current creator chain passes through lem-sfb-dc-hom-small-coefficients to a module name, rather than an imported node, and tools/blueprint_refs.py ancestor prints None. I preserve that mechanical provenance and its explicit from.place, which identifies the algebraic-closure paragraph of lem-sfb-dc-hom-preserves and the old live step 9. The report identifies the current immediate parent step 4. Whole-blueprint searches for internal Hom comparison, filtered finite and filtered continuity found no identical imported node; the general comparison is an existing created node and is reused. No fabricated ancestor or same_as entry was added.

## Mathlib searches

All five new searches were executed through the prescribed msearch.py command and their actual outputs read. Both LeanFinder phrasings returned sheaf free-object naturality, ordinary finite-dimensional internal Hom, and ambient LightCondensed closed structures. LeanSearch returned ModuleCat.extendScalars/coextendScalars and ordinary algebra scalar-extension tools. These do not prove a derived internal-sheaf comparison over an algebraic-closure coefficient ring under the stated continuity. Loogle with the exact query recorded in searches.jsonl and the coefficient/internal-Hom grep returned no hits. All services answered successfully; none was recorded as unavailable. The existing inherited Q22 searches are retained, and the five Q34 searches are appended exactly from the log.

## Not duplicates

No new nodes were created. The whole-DAG statement search found lem-sfb-dc-hom-filtered-colimit as a strict generalization of the desired comparison; it is cited in step 5. The finite-freeness assertions, subextension algebra, coefficient-ring colimit, tail module colimit, and exactness infrastructure also already exist. I checked the generic comparison's dependency closure: it does not reach this item, so its reuse does not create a cycle.

## Review by Q34

I read the stage-1 brief, worker role, stage document, GOAL.md, the three fixed blueprint levels in SETUP.md, the item's chapter/unit records, and both copies of delivery-errors.md B–E. I read Bhatt–Scholze at the places above, the current main blueprint's lem-sfb-dc-hom-preserves proof and coefficient finite-freeness statement, and Stacks sites-modules.tex at Tags 03DA/03DB/03CO and 03EP/03EU, plus sites-cohomology.tex at Tag 08J9 (lemma-internal-hom). There are no new-node sources to check. In particular no printed theorem is silently promoted to an assertion about arbitrary unbounded complexes: the existing general comparison is the explicit bridge.

Step 1 uses def-weil-size-convention for the universe containing the coefficient set and small skeleton. det-def-sfb-qlbar-condensed-subextensions states the finite-compositum assertion itself, not just the definition of an algebraic closure. The proof applies it to F,G and to E,H. The tail is nonempty because E is present; for each H the objects above H in the tail are directed. Smallness is a set-of-subfields argument in the stipulated universe. This verifies cofinality without invoking an unstated small-index theorem.

Step 2 uses assertion (2) of sk-prop-sfb-cartesian-coefficients, which unconditionally says F_X is finite free over E_X. I deliberately use that assertion instead of asking a statement conditional on a chosen integral basis to prove existence of the basis. E=F is handled by the identity and rank one. The two coefficient-map definitions identify exactly the inclusions used for transitions and closure legs. No twist or invertibility-of-ell hypothesis is used; the cited node explicitly exempts its untwisted assertions from that hypothesis.

Step 3 uses lem-sfb-subfield-coefficient-map-comp for the closure-leg equation. sk-prop-sfb-qlbar-colimit-x states the ring-sheaf colimit with field-inclusion transitions; it does not alone assert the module colimit, so the latter is taken separately from lem-sfb-qlbar-tail-module-colimit. The tail ring-colimit argument is written out using the cocone definition: t_H is obtained from t_EH, inclusion of H in J gives inclusion of EH in EJ, and EF=F gives the restriction and uniqueness. For algebra cocones the E leg forces compatibility with the structural S map. This is a short universal-property calculation, not a new lemma hidden under the word cofinal. The module-tail statement also fixes the actions and the actual q_F maps, so no arbitrary isomorphism of colimit objects is substituted.

Step 4 uses the exact, faithful module forgetful functor and its colimit preservation, all explicitly stated in lem-weil-pbc-module-sheaves-colimits-forgetful. The abelian-sheaf exactness theorem is the statement of lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact. Reflection of vanishing through a faithful functor proves the reflection of exactness in a few lines. Both apply on the chosen small site and to the same coefficient-universe index; no existence theorem for only finite or countable colimits is used.

Step 5 reads the statement of lem-sfb-dc-hom-filtered-colimit, not its proof. It assumes exactly a small filtered diagram of finite-free commutative algebra sheaves, an algebra/module colimit, exact filtered module colimits, internal-sheaf continuity on the fixed index, and a second input bounded below in cohomology. Steps 1–4 establish each of those. The item has continuity for every small filtered diagram, which implies the fixed-index requirement. Its L bound is unchanged, and the general theorem explicitly uses a bounded-below representative while allowing the Hom complex itself to be unbounded. Its conclusion contains exactly the canonical comparison in D(T), the restricted three-arrow formula and all evaluation/naturality/transition/basis clauses. This is reuse of an existing general theorem, not moving this item's argument into a new clause-node. The generic theorem is in this unit; statements from other units are declared as coefficient-algebra or abelian-category tools in split_report.tool_uses.

For B1–B9 there are no new nodes and no Mathlib-leaf assertions; statement objects are introduced, TeX remains correctly encoded, and searches are honest. For B10 I checked the upstream tag and notion searches before splitting. For C1–C4 every non-elementary input above is a cited statement, with all twelve quotations checked against those statements, never against their proofs. For C5–C8 existing results are reused, the dependency closure has no back edge, and off-unit tool uses are explained. For D1–D5 no restatement node is introduced and the nontrivial specialization hypotheses are verified explicitly. For E1–E7 the ring maps, module actions, finite-field index, lower bound and exactness hypotheses were compared with each cited statement. There is no source error or disputed statement.

Edge cases checked: X empty (zero module category), K=0 and L=0 (zero comparisons), F=E (identity coefficient extension), E=Q_ell, finite diagrams/single-stage specialization of the generic theorem, and L shifted into any lower degree. Finite-stage maps need not be quasi-isomorphisms of coefficient algebras; only finite freeness is used. No Noetherian, finite type, constructibility, site-perfectness or completeness assumption is introduced. All five proof steps are under 2000 characters; none hides a long auxiliary comparison.

## Unfinished work

None in this one-level split. The new proof is ready for the required server preflight and independent maintainer review.
