# Stage-1 worker report: lem-sfb-comap-preserves-k-injectives

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-comap-preserves-k-injectives.json`: existing statement node, split into three proof steps. The statement is unchanged. No Mathlib match.
- `citations.json`: seven verbatim statement quotations, covering every step citation.
- `searches.jsonl`: original search evidence retained and four additional actual searches appended by msearch.py.
- No new nodes and no new Mathlib leaves. `repair.py` is sandbox-only preparation code and is not part of the delivery.

## Attachments

None for this item. The slopmaster2 source has no occurrence of the item's tag or named coefficient-change instance; its other `preservesKInjectiveComplexes` occurrences concern different functors. The existing generic declaration `CategoryTheory.Adjunction.preservesKInjectiveComplexes` at `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Comp.lean:95` belongs to `lem-weil-pbc-right-adjoint-preserves-kinjective`; its body is sorry-free and the existing node's slopmaster2 audit is closed. It is reused without editing that node.

The upstream master reference does contain `AlgebraicGeometry.ProEtale.CondensedRing.preservesKInjectiveComplexes_comap_coefficientMap` in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:211`. Its proof applies the generic theorem under the finite-limit hypothesis on extension of scalars. As instructed, this separate master reference is not used as evidence of a finished slopmaster2 attachment.

## WANTED

None.

## What was wrong and what changed

The earlier sandbox attempt quoted “Likewise Mod is a ... Grothendieck abelian category” from the proof of `sk-def-sfb-derived-categories`, although this is absent from that node's statement. This violates C3/C4 and its citation would fail the verbatim statement check. The old scalar-change quote was also stale: the shared node now states finite-colimit preservation in clause 2, not in the quoted clause-4 sentence. I replaced both with current statement quotations and made the setup explicit.

Step 1 now takes ambient abelianness from the abelian-category clause of `lem-weil-pbc-site-sheaves-enough-injectives`. It takes the tensor structure and preservation of colimits from `sk-def-sfb-sheaf-tensor`, the ring-object map from `sk-def-sfb-coefficient-change`, and module abelianness, the Ext–Res adjunction and preservation of finite colimits from clauses 2–4 of `sk-def-sfb-change-of-scalars`. Step 2 writes the short additivity argument and uses the hypothesis at X to obtain exactness. Step 3 applies the existing general exact-adjoint theorem. No new lemma restates the item, and no new nodes are needed.

The imported node's original proof gave the Hom_K argument but cited only scalar change. The split now records all inputs used. There is no statement dispute, changed coefficient category, added boundedness hypothesis or departure from the chapter/unit route.

## Searches and reuse

I searched all DAG nodes and the imported blueprint using `tools/blueprint_refs.py search` for `K-injective`, `restriction of scalars`, and `comap-preserves-k-injectives`, and checked the item's blueprint ancestor. The generic Stacks 08BJ node is more general; no other blueprint node states precisely the coefficient-change specialization, so `blueprint.same_as` is empty and `from` remains null for this imported node. Searches by tag 08BJ and `lemma-adjoint-preserve-K-injectives` confirmed reuse rather than creating a duplicate. There are no new-node pairs requiring a Not duplicates entry.

The original logged searches are retained. The repeated searches, all run through msearch.py, were:

- leanfinder: `A right adjoint to an exact additive functor between abelian categories preserves K-injective cochain complexes`;
- loogle: `CochainComplex.IsKInjective`;
- grep: `IsKInjective|KInjective` in `Algebra/Homology`;
- leansearch: `A right adjoint of an exact functor preserves homotopically injective complexes`.

All four services returned results. I read the KInjective source at `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`, especially lines 35–99 and the remaining declaration list. The results define K-injectivity, establish homotopy/shift invariance or prove K-injectivity of bounded-below injective complexes; the semantic searches also found injective-object preservation under adjunctions and derived exact-functor maps. None states this unbounded scalar-change result or its abstract exact-adjoint generalization. The project already supplies the abstract theorem, so no Mathlib leaf is claimed.

## Review by Q39

I read the current chapter record `sec-six-functors-basics`, the unit record `sk-def-sfb-coefficient-comparisons` (especially its third step), and both the statement and proof files of the item in `literature/blueprint/main-20261015/`. The statement retains the morphism of commutative condensed rings, the hypothesis for every scheme X, the correct direction from Lambda'-modules to Lambda-modules, and arbitrary unbounded K-injective complexes. The unit uses precisely this preservation assertion in its derived comparison construction; the split does not replace that route.

For step 1 I opened all four cited node statements. `lem-weil-pbc-site-sheaves-enough-injectives` explicitly says the category of abelian sheaves is abelian. I checked its supporting source, Stacks tag 03CN (`sites-modules.tex`, `lemma-abelian-abelian` (1)); the enough-injectives part is unused. The small pro-etale representative is taken in the chosen universe, so the site's size condition is met. `sk-def-sfb-sheaf-tensor` explicitly supplies a symmetric monoidal structure, closedness, and preservation of colimits on either side, with Ab as an explicit example. The tensor additivity needed by clause 4 follows in the written step from preserving zero and binary coproducts via the biproduct formula, rather than from an uncited stronger theorem. Equalizers and coequalizers are kernels and cokernels of differences in the ambient abelian category. `sk-def-sfb-coefficient-change` explicitly identifies a_X as a ring-object morphism between the two pulled-back coefficient rings. Its source and the scalar-change definition were read. The current statement of `sk-def-sfb-change-of-scalars`, not merely its proof, supplies the Ext–Res adjunction, finite-colimit preservation and abelian module categories under exactly the braided/closed/(co)equalizer/tensor hypotheses just verified. No sheaves-of-modules versus module-objects equivalence is being assumed: these are the module-object categories of the coefficient setup throughout.

For step 2 I reread scalar-change clause 1: restriction is the identity on underlying objects and arrows, hence preserves their additive sums. Extension's additivity is written out from its finite-colimit preservation: it preserves zero maps, coproduct inclusions and the projections characterized by identity and zero, hence diagonal/codiagonal addition. Its preservation of finite limits is precisely the item hypothesis specialized to the fixed scheme X; no flatness beyond that hypothesis is inserted. I read Stacks tag 0034 (`categories.tex`, `definition-exact`) and the complete statement of the cited `def-galois-exact-functor`. Both define exactness as simultaneous left and right exactness. This step is elementary because it uses the recorded preservation results and the displayed biproduct calculation.

For step 3 I read the entire statement of `lem-weil-pbc-right-adjoint-preserves-kinjective`, the proof of Stacks tag 08BJ (`derived.tex`, `lemma-adjoint-preserve-K-injectives`), and the slopmaster2 declaration's actual body. The node requires additive u and v, abelian A and B, v left adjoint to u, and v exact; steps 1–2 establish each with A = Lambda'_X-module objects, B = Lambda_X-module objects, u = Res and v = Ext. The node explicitly concludes preservation of K-injective complexes under termwise u; its statement uses the homotopy-vanishing notion required here. Its proof/source gives exactly the blueprint's Hom_K adjunction and vanishing argument, so I do not claim extra homology or homotopy consequences from a definition-only node.

I checked the zero coefficient ring and zero complex, the empty scheme, the identity coefficient map, and complexes unbounded in both directions. No step requires a nonzero object, a point of X, invertibility of a, boundedness, injective terms, or the flatness of an ordinary discrete ring in place of the stated categorical hypothesis. No new statements were introduced to test. I checked B–E: the new-node-only format requirements are vacuous; every non-elementary input is a cited statement; the elementary step is fully written; there is no moved clause or circular new node. I traversed the existing statement/proof dependency graph from each cited input and found no path back to the item. The off-unit site-category fact and generic K-injective theorem are recorded as tool uses in the split report. All seven citations are verbatim parts of their current node statements.

The concrete repairs to the prior attempt are the removal of the proof-only derived-category citation, replacement of the stale scalar-change quote, explicit checking of the ambient and additive hypotheses, separation into three numbered steps, and a second phrasing of the Mathlib search. The author's review above is for the fresh independent reader to check; it is not an independent second reading.

## What I could not finish

Nothing remains in the mathematical split. The required delivery dry run is being run; its result is recorded in `dry-run.log` in the sandbox. No push is authorized in this worker turn.

## Second reading by Q39

- Item statement: reread the blueprint node and its proof source `lem-sfb-comap-preserves-k-injectives.md` / `.proof.md`; the morphism `a`, the per-scheme finite-limit hypothesis on `Ext_{a_X}`, the direction of `Res_{a_X}`, and arbitrary unbounded K-injective complexes agree hypothesis by hypothesis. Tested the identity coefficient map, the zero complex, the empty scheme, and an arbitrary scheme; no nonzero, boundedness, flatness, or point hypothesis is hidden.
- Step 1: reread all four cited statements. The site-sheaf node supplies the abelian ambient category; the sheaf-tensor node supplies closed symmetric monoidal structure and colimit preservation; coefficient-change supplies the ring-object map; change-of-scalars clauses 2–4 supply the module categories, `Ext \dashv Res`, finite-colimit preservation, and the relevant module-category hypotheses. The biproduct additivity observation is elementary from those statements. The pro-étale site and module notation are the definitions used by the derived-categories/coefficient-change statements; no proof-only fact is imported.
- Step 2: reread clauses 1 and 2–4 of `sk-def-sfb-change-of-scalars` and `def-galois-exact-functor`. Restriction is additive because it is identity on underlying arrows; extension is additive by preservation of zero and binary coproducts and the biproduct formula; the item hypothesis supplies finite limits, while clause 2 supplies finite colimits. Thus exactness follows exactly from the cited definition. The step is marked elementary and contains the calculation needed to check it. I checked the exactness definition against Stacks `categories.tex`, label `definition-exact` (tag 0034), and ambient abelianness against `sites-modules.tex`, label `lemma-abelian-abelian` (tag 03CN), clause 1.
- Step 3: reread the complete statement of `lem-weil-pbc-right-adjoint-preserves-kinjective` and Stacks tag 08BJ. Its hypotheses are additive functors between abelian categories, `u` right adjoint to exact `v`; steps 1–2 instantiate these with `u = Res` and `v = Ext`. Its conclusion is precisely termwise preservation of K-injectivity, including the unbounded case. No proof detail is taken from a node beyond its statement. The source checked was `derived.tex`, lines 9857–9878, label `lemma-adjoint-preserve-K-injectives`; its Hom in the homotopy category vanishes after applying the exact left adjoint, exactly as in the blueprint proof.
- New nodes: none. I checked the whole DAG for duplicates of the coefficient-change specialization, restriction-of-scalars K-injectivity, and the cited abstract theorem; the existing abstract node is reused. Therefore B1–B7 and new-node source/search requirements are vacuous.
- C1–C4 and E checks: every non-elementary input in the three steps is named by a cited node whose statement was opened and matched; no tag is used as a substitute for a node, no cited proof-only claim is used, and there is no cycle back to the item. The zero coefficient ring, identity map over a field, empty scheme, degree-zero complexes, and two-sided unbounded complexes leave every step valid. The source route and coefficient categories are unchanged.
- Changes made in this second reading: none to the DAG node, citations, or search log; appended this independent review section only. The prior worker's stale proof-only citation and stale scalar-change quotation are already removed in the current files.

All seven entries in `citations.json` were checked as verbatim substrings of the current cited node statements. A fresh traversal of the statement and proof dependencies from each of the six distinct proof inputs found no path to this item. The closed generic theorem was also read in the slopmaster2 source; the coefficient-change specialization occurs only in the separate master reference, so no new attachment is claimed.
