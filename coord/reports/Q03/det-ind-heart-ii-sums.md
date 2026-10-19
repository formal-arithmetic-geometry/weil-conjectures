# Worker report: det-ind-heart-ii-sums

## Files written

- `dag/nodes/sec-six-functors-basics/det-ind-heart-ii-sums.json`: retained the typed, corrected auxiliary statement and three proof steps; the statement correction is documented under `## Source error` below and authorized by the current repair brief.
- `report.md`: replaced the earlier inconsistent review, added the exact `## Source error` section and recorded the E7b repair.
- `citations.json`: retained the six verbatim quotations after checking them against the current cited statements.

There are zero new nodes and zero Mathlib leaves. The retained `mathlib_searches` and `searches.jsonl` were not replaced or supplemented with invented searches.

## Attachments

None. In this repair I searched the read-only `WeilConjectures/` trees in slopmaster2 and upstream master by the exact blueprint id, `IndCons`, ind-constructible vocabulary, and Ext/sum/coproduct vocabulary. No declaration stating the item was found. The slopmaster2 file `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean` concerns finite coproducts in the first argument and vanishing, which does not state this item. No attachment is claimed from sorried upstream source.

## WANTED:

None. The exact current blueprint statement and proof, dependency statements, and Stacks module-category sources are available locally.

## What was wrong or corrected

E7b has two parts: the statement adds a Noetherian hypothesis absent from the exact blueprint detail, and the claimed counterexample lacked the required `## Source error` section. The current repair brief authorizes correcting an ill-typed, false, or under-hypothesized imported statement; that correction and its counterexample are recorded below. I did not erase the counterexample or pretend Noetherian is already implicit in the chapter: the chapter, unit and item text I read do not state it. Merely restoring the imported sentence while continuing to apply a Noetherian theorem would leave an E1 hypothesis gap.

The current human repair brief explicitly instructs: “If the imported statement is ill-typed, false, or missing hypotheses, mark STATEMENT-DISPUTED in report.md, give the explicit counterexample or type check, correct the statement faithfully to the source's intent, and continue the split.” I follow that authorization for this auxiliary detail. The corrected statement is kept in the split-owned `statement` field. The complete correction record is `split_report.statement_change`, reproduced below, with the exact old and new statements, the current human authorization, counterexample, source scope, old dependencies/proof and every direct citer. This is nested review information inside the stage-1-owned split report; it does not set the top-level `statement_change` field reserved by the tools for stage-2 corrections. The correction is reported openly for the second reader and maintainer to assess. No archived target or chapter/unit record is changed.

The substantive proof is the same three-step blueprint route that the return accepted: finite biproduct additivity, the finite-subset colimit, and the reviewed constructible Ext-continuity lemma. The correction makes the hypothesis of that last lemma available rather than assuming it silently.

## Source error

STATEMENT-DISPUTED: the current `main-20261015` detail `sk-cor-ind-heart-ii-sums.md` leaves X unbound and gives no scheme hypothesis. Read as a claim for arbitrary schemes, it is false already for q=0, with the affine-local constructibility definition actually in the DAG. The chapter and parent unit do not remove this example by stating a global Noetherian convention.

Fix a prime ell, choose an algebraically closed field k of characteristic different from ell, a finite extension E/Q_ell, and let X be the countable disjoint union of copies X_n = Spec(k). Let C = E_X be the regular module for the pulled-back condensed coefficient ring, and let B_n be its restriction to X_n extended by zero to all other components. Each B_n and C is constructible in the existing definition: any affine open U is quasi-compact, so its covering by the disjoint open subsets U intersect X_n has a finite subcover. It meets finitely many components. On each of these open-and-closed strata the sheaf is a regular rank-one module or the zero module, both finite constant local models. Constant filtered diagrams show that each B_n is ind-constructible.

Sheaves and module structures on a disjoint union are families on its components: the sheaf gluing condition for the component cover gives this description, and restrictions and gluing are inverse. Coproducts are consequently computed componentwise in this product category. On component m, exactly B_m is E_{X_m} and the others vanish. Thus the categorical sum of the B_n is C. Any element of the direct sum of the degree-zero Hom groups has only finitely many nonzero component maps C -> B_n. Its image as an endomorphism of C is zero on every component outside that finite set. The identity of C is nonzero on every component, since each regular coefficient module is nonzero. It cannot be in the image. This proves failure of surjectivity without needing an identification of the coefficient sections or any claim about higher Ext.

The faithful source-route repair is the existing Noetherian scope of `sk-lem-constructible-ext-continuity`. Its complete reviewed statement starts with Noetherian X and explicitly includes the constructible-sheaf clause for E and Qlbar used in this proof. Its generation input `det-cor-coefficient-heart-ii-generation` likewise explicitly starts with Noetherian X. I retain that hypothesis in this auxiliary item's statement, preserve every original conclusion and coefficient choice, and record the change explicitly rather than claiming it is verbatim in the blueprint. No SGA source is used.

The complete direct-citer search of current `dag/nodes/*/*.json`, checking both `stmt_deps` and `proof_deps`, found exactly `det-constructible-compactness-bounded`. I opened its statement and Step 3. It assumes X separated finite type over a field k, so its hypothesis implies the repaired one: k is Noetherian since its only ideals are 0 and k, and the existing `lem-weil-pbc-finite-type-over-noetherian` explicitly makes a finite-type scheme over a Noetherian scheme Noetherian. Its use is the all-integer Ext-sum comparison and stays valid. This direct-citer audit is recorded here with its reason; no citer was edited. The parent unit's unrestricted prose has the same source omission; I report it for maintenance without changing that fixed record.

## Statement corrected

The following is the exact structured record retained at `split_report.statement_change`. In particular, `old_statement` is the current shared-base statement verbatim; no hypothesis is represented as already present in the blueprint.

```json
{
 "date": "2026-10-16",
 "by": "Q03 stage 1",
 "old_statement": "Let $\\Lambda=E$ or $\\Qlb$, $C\\in\\Cons(X,\\Lambda)$, $q\\in\\mathbf Z$, and let $(B_s)_{s\\in S}$ be a family in\n$\\IndCons(X,\\Lambda)$. The natural map\n\n$$\n\\bigoplus_{s\\in S}\\Ext^q(C,B_s)\\longrightarrow\\Ext^q\\Bigl(C,\\bigoplus_{s\\in S}B_s\\Bigr)\n$$\n\nis an isomorphism.",
 "new_statement": "Let $X$ be a Noetherian scheme, meaning locally Noetherian ([pqf-def-locnoeth]) and quasi-compact ([def-weil-pbc-quasi-compact-scheme]). Fix a prime $\\ell$, an algebraic closure $\\Qlb$ of $\\mathbf Q_\\ell$, and a finite subextension $E/\\mathbf Q_\\ell$ in $\\Qlb$. Let $\\Lambda=E$ or $\\Qlb$, with coefficient ring object $\\Lambda_X$ as in [def-sfb-subfield-coefficient-ring] or [def-sfb-qlbar-coefficient-ring], respectively. Write $\\mathcal A=\\Mod_{\\Lambda_X}$ for the category of module sheaves on $X_{\\mathrm{proét}}$ ([sk-def-sfb-module-objects]), and $D(\\mathcal A)$ for its unbounded derived category ([def-weil-abstract-derived-category]). Let $\\Cons(X,\\Lambda)$ denote the full subcategory of constructible module sheaves ([sk-def-sfb-constructible]), and let $\\IndCons(X,\\Lambda)$ denote the full subcategory of small filtered colimits in $\\mathcal A$ of objects of $\\Cons(X,\\Lambda)$.\n\nFor $C\\in\\Cons(X,\\Lambda)$, $q\\in\\mathbf Z$, and a family $(B_s)_{s\\in S}$ in $\\IndCons(X,\\Lambda)$ indexed by a set $S$, define $\\Ext^q_\\Lambda(C,B)=\\Hom_{D(\\mathcal A)}(C,B[q])$, with sheaves placed in degree zero. The natural map induced by the coprojections $B_s\\to\\bigoplus_{s\\in S}B_s$,\n\n$$\n\\bigoplus_{s\\in S}\\Ext^q_\\Lambda(C,B_s)\\longrightarrow\\Ext^q_\\Lambda\\Bigl(C,\\bigoplus_{s\\in S}B_s\\Bigr),\n$$\n\nis an isomorphism. The sum on the left is in abelian groups and the sum on the right is in $\\mathcal A$.",
 "what": "The blueprint leaves X unbound and states no global Noetherian convention. Its unrestricted reading is false in degree zero on a countable disjoint union of algebraically closed points. Add the Noetherian scope already required by the cited constructible Ext-continuity lemma, and bind the coefficient ring objects, ordinary derived category, IndCons and Ext explicitly; preserve both coefficient choices and every integer degree.",
 "authorization": {
  "source": "Current dispatcher repair brief, Statement disputes are repaired, never abandoned",
  "instruction": "If the imported statement is ill-typed, false, or missing hypotheses, mark STATEMENT-DISPUTED in report.md, give the explicit counterexample or type check, correct the statement faithfully to the source's intent, and continue the split."
 },
 "source": {
  "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-cor-ind-heart-ii/sk-cor-ind-heart-ii-sums.md",
  "place": "node det-ind-heart-ii-sums, order None"
 },
 "counterexample": "Take X = coproduct over n in N of Spec(k), k algebraically closed of characteristic different from ell; C = E_X and B_n its regular module on component n and zero elsewhere. All are affine-locally constructible. Their coproduct is C componentwise. Every finite sum of maps C -> B_n vanishes off finitely many components, whereas id_C is nonzero on every component. Therefore the degree-zero comparison is not surjective.",
 "citers": [
  {
   "id": "det-constructible-compactness-bounded",
   "holds": true,
   "note": "Its separated finite-type scheme over a field is Noetherian, by lem-weil-pbc-finite-type-over-noetherian applied to Spec(k), and its Step 3 uses exactly the preserved all-integer Ext-sum comparison."
  }
 ],
 "old_stmt_deps": [],
 "old_proof": [
  {
   "text": "For a finite subset $T\\subset S$, the map $\\bigoplus_{s\\in T}\\Ext^q(C,B_s)\\to\\Ext^q(C,\\bigoplus_{s\\in T}B_s)$\nis an isomorphism because $\\Ext^q(C,-)=\\Hom(C,-[q])$ is additive and finite direct sums are biproducts.\nThe sum $\\bigoplus_{s\\in S}B_s$ is the filtered colimit, over the finite subsets $T$ ordered by\ninclusion, of the sheaves $\\bigoplus_{s\\in T}B_s$ in degree $0$. By part (1) of\n[sk-lem-constructible-ext-continuity],\n\n$$\n\\Ext^q\\Bigl(C,\\bigoplus_SB_s\\Bigr)=\\varinjlim_T\\Ext^q\\Bigl(C,\\bigoplus_TB_s\\Bigr)\n=\\varinjlim_T\\bigoplus_T\\Ext^q(C,B_s)=\\bigoplus_S\\Ext^q(C,B_s),\n$$\n\nand the composite is the natural map.",
   "uses": [
    "sk-lem-constructible-ext-continuity"
   ],
   "elementary": false
  }
 ],
 "old_proof_deps": [
  "sk-lem-constructible-ext-continuity"
 ]
}
```

## Not duplicates

No new nodes were created. The retained split reuses the existing general ringed-site category theorem and the existing continuity theorem. Finite biproduct identities and the finite-subset universal-property argument are elementary proof steps; they are not helper nodes or restatements of this item's clause. The retained whole-DAG and blueprint searches had found neighboring ind-heart statements, including filtered-colimit closure, but these do not supply a different Ext-continuity statement.

## Review by Q03

I read `coord/brief-stage1.md`, the stage-1 instructions, SETUP's three levels, GOAL, dag-sync, and delivery-errors B through E. For this repair I opened the actual chapter and unit JSON records, `dag/chapters/sec-six-functors-basics.json` and `dag/units/sk-cor-ind-heart-ii.json`, together with their current blueprint `_section.md` files. These records do exist; the previous report incorrectly said they did not. I opened the exact item statement `sk-cor-ind-heart-ii-sums.md` and its complete proof `sk-cor-ind-heart-ii-sums.proof.md`. The three steps follow its route exactly. The scheme correction is explicitly distinguished above from the source's literal wording.

I opened the full statements of all seven statement dependencies: `pqf-def-locnoeth` and `def-weil-pbc-quasi-compact-scheme` give the two conditions in the stated definition of Noetherian; `def-sfb-subfield-coefficient-ring` and `def-sfb-qlbar-coefficient-ring` give the pulled-back condensed ring objects, rather than discrete constant coefficients; `sk-def-sfb-module-objects` gives the module-object category; `def-weil-abstract-derived-category` gives the ordinary unbounded derived category; and `sk-def-sfb-constructible` gives finite constant local models and affine-local constructibility on arbitrary schemes. IndCons and Ext are explicitly defined in the item. Its coefficients and derived category agree with those of the cited continuity theorem.

Step 1 uses the module-object definition, `lem-pur-ringed-site-grothendieck-abelian`, the derived-category definition and `def-weil-triangulated-category`. I read each entire statement. A module action in abelian sheaves is precisely a sheaf-module action: the tensor universal property identifies its bilinear action with the sectionwise scalar action, with the same unit and associativity equations. The general ringed-site theorem supplies the abelian category and small colimits for the small site in the chosen universe and the commutative coefficient sheaf. I also read Stacks `sites-modules.tex`, labels `lemma-abelian` and `lemma-limits-colimits`, Tags 03DA and 03DB: these state the required abelian and colimit properties. The derived-category definition gives the additive derived category and the localization induced from complexes, and the triangulated definition makes every integer shift additive. The displayed finite inclusion/projection identities therefore survive in the shifted derived category and give the two inverse Hom maps written in the step. The same coprojection equation verifies compatibility for inclusions of finite subsets. This is the elementary part, including the empty finite subset.

Step 2 uses that same ringed-site theorem only to ensure the required colimits and coproducts exist. I checked its statement says so, rather than inferring a property from a definition. The rest is the written universal-property proof: singleton components determine each finite-sum leg of a compatible cocone, and every family of singleton maps supplies those legs. This identifies the filtered colimit with the full coproduct both in module sheaves and in abelian groups. Fin(S) is a set-sized category, contains the empty subset, and union provides upper bounds; a poset has no further parallel-arrow condition. This includes the empty family and avoids the false assertion that arbitrary sheaf sums are computed sectionwise.

Step 3 uses exactly the constructible-sheaf conclusion of `sk-lem-constructible-ext-continuity`. I opened its whole current statement, including its initial Noetherian hypothesis, coefficient specification and every-integer-degree conclusion. The restored explicit Noetherian hypothesis in this corrected auxiliary item supplies its missing assumption. All B_T are degree-zero complexes, so they have common lower bound zero. Fin(S) is small and filtered by Step 2. The cited theorem accepts arbitrary module sheaves as its second argument, so no extra lemma saying finite sums are ind-constructible is needed. The compatible inverses from Step 1 induce inverse colimit maps. A class from the s-th summand enters at {s} and is sent to its composite with the shifted coprojection; hence the composite is exactly the natural map in the statement.

The six entries of `citations.json` were checked against the current dependency statements, including the same ringed-site theorem used in two steps; each quote is verbatim after whitespace normalization. Every non-elementary input is cited where used, `proof_deps` is precisely the union of step citations, and no cited node requires using hidden details of its proof. The general ringed-site theorem is declared in `split_report.tool_uses`, solely as an ambient-category tool; it replaces no unit step. The maintainer-owned `tool_uses` field was not edited.

I checked empty X, zero C, empty and singleton S, finite and infinite S, q=0 and negative q. The finite-biproduct argument works in every integer shift. For a finite disjoint union of points the degree-zero map has finite support automatically; the countable disjoint union demonstrates exactly why the unrestricted source is false. The corrected Noetherian scope is the scope of the reviewed continuity result, and the sole direct citer satisfies it. I did not try to treat the unrestricted source as proved by an out-of-domain citation.

For B, there is no new statement-only node or leaf, and the item binds its own objects and definitions. For C, I checked every cited statement, the smallness conditions, coefficient agreement and dependency coverage. For D, the finite-sum and colimit arguments remain in this item; no conclusion has been moved into a child. For E, the initial Noetherian hypothesis is now justified by the explicitly authorized auxiliary correction, and the counterexample, exact change and affected citer are recorded rather than hidden. No target or unit statement was changed.

The retained Mathlib records have actual corresponding search-log entries. I read those results: generic condensed AB4/AB5, additive Ext identities and finite biproduct infrastructure do not state the constructible pro-etale arbitrary-sum theorem. Earlier invalid Loogle identifiers remain labeled invalid; they are not negative evidence. No new node or Mathlib leaf is claimed, and no new search was fabricated during this repair. The previous reader's source searches and the current repair's read-only project search found no exact attachment.

## E7b repair and verification

1. The Noetherian addition is an explicitly reported `STATEMENT-DISPUTED` correction authorized by the current repair brief. The corrected statement remains in the split-owned `statement` field; the old literal wording, counterexample, intended source scope, and direct-citer check are all written in `## Source error` above. The required structured record is now retained explicitly at `split_report.statement_change` and reproduced in this report; no stage-2 top-level correction field is set.
2. The report contains the exact heading `## Source error`, a fully specified degree-zero counterexample, the true source-route scope, and the effect on the current direct citer. It no longer presents the added hypothesis as part of the literal blueprint statement.

## Dry-run result

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q03 det-ind-heart-ii-sums --no-push` printed `OK (not pushed) deliver/Q03/det-ind-heart-ii-sums at 2a1bdc0265: preflight passed`. The tool rebuilt the delivery on the current fetched base. A final dry run includes this completed report. Nothing was pushed. No Lean file, compiler, Lake command, live project file or launcher tool was changed.

Compared with the returned version described at c4e876b984, this repair adds the explicit source-error report and complete structured correction audit. Compared with the current shared base, the record retains the old statement verbatim and lists the sole direct citer. The mathematical three-step split is retained, as the return accepted its steps and citations.

## Second reading by Q03

- Item statement: checked against `sk-cor-ind-heart-ii-sums.md` and the Noetherian hypothesis of `sk-lem-constructible-ext-continuity`; the unrestricted imported wording is false, and the reported Noetherian correction preserves the intended route and both coefficient cases.
- Step 1: checked finite biproduct identities and shifts against the statements of `sk-def-sfb-module-objects`, `lem-pur-ringed-site-grothendieck-abelian`, `def-weil-abstract-derived-category`, and `def-weil-triangulated-category`; verdict: all cited facts are available and the finite inverse maps are explicitly written.
- Step 2: checked the filtered finite-subset colimit argument against `lem-pur-ringed-site-grothendieck-abelian`; verdict: the filteredness, smallness, empty family, and coproduct universal property are stated, with no sectionwise-sum assumption.
- Step 3: checked the continuity application against the complete statement of `sk-lem-constructible-ext-continuity`; verdict: its Noetherian, coefficient, bounded-below, and all-integer-degree hypotheses are supplied and the natural-map identification is explicit.
- New nodes: none; consequently there are no new statement-only nodes, Mathlib leaves, duplicate nodes, or node searches to repair. Existing dependencies were checked by id and full statement against the shared DAG.
- Changes made in this second reading: added this required audit section; retained the corrected statement and three proof steps because no further mathematical or dependency repair was necessary. The source counterexample, authorization, and direct-citer audit remain in `## Source error` and `split_report.statement_change`.
