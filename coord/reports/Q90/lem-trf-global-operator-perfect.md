# Stage-1 report: lem-trf-global-operator-perfect

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-global-operator-perfect.json`: split statement, unchanged statement, four proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for each of the sixteen step citations.
- `report.md`: this report, replacing the earlier attempt's accumulated reviews.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, its blueprint tag and combinations of globalOperator/perfectness. I read `SixFunctors/ProEtale/TraceFormula/Correspondence.lean:808–869`. The declarations `globalOperatorUnit`, `globalOperatorCounit` and `globalOperator` construct arrows under a geometric operations package; none states that every intermediate coefficient complex is perfect. They therefore do not attach this item.

## WANTED

None.

## What was wrong and what changed

The imported item has one paragraph containing several preservation assertions without a preservation theorem citation. Its appeal to item (3) of strong ambient exceptional-adjoint admissibility also conflicts with the current constructible-only admissibility definition. The earlier sandbox repaired this by citing the existing generic `thm-sf-ctf-stability`. I retained that mathematical repair and wrote the argument in four steps, each checked directly against the statements it cites. The statement is unchanged and agrees with the current main-20261015 blueprint.

The earlier Mathlib grep entries used `Mathlib/Algebra/Homology` as the subdirectory argument, but msearch.py already prepends Mathlib/. Those empty results were not valid negative evidence. I replaced the item's search records with seven searches freshly run in this audit, including correct `Algebra/Homology` paths and a grep of all Mathlib. The older invalid searches remain only in the append-only tool log. I read every returned hit. Continuous/group cohomology, abstract derived categories, etale rings, finitely presented sheaves and topological compact supports do not state this item. Two distinct semantic phrasings were tried; all four search kinds ran successfully. Exact query strings and tool summaries are recorded in mathlib_searches.

## Unfinished work

None at this split level. Existing dependencies remain their own items. No push or compiler invocation was made; a fresh second reader is to review and deliver this sandbox after the successful dry run.

## Review by Q90

I read the chapter record `sec-trace-formula`, the unit record `sk-d-operator`, the current main-20261015 item statement and `.proof.md`, and its imported master source. The unit's route is the ordinary unit, proper comparison, correspondence map, compact-support composition and exceptional counit. All are retained. The item still assumes finite coefficients A=O_E/varpi_E^n, n>=1 and ell different from p, K finite-Tor constructible, an admissible correspondence of separated finite-type schemes, and proper ordinary leg c_2. It still proves perfectness of every intermediate object, rather than only the endpoints.

For step 1 I opened the current statements of coefficient conventions, correspondence, admissibility, proper morphism, global operator, compact-support perfectness and categorical trace. Correspondence gives separated finite-type X,C; admissibility has separated finite-type c_1 as its domain; properness gives precisely separatedness and finite type of c_2. I also read Stacks morphisms.tex, definition-proper (01W1), and schemes.tex, definition-separated (01KK), confirming these uses of the existing proper-morphism node. Both structure maps are separated finite type, so compact-support perfectness applies to K. The categorical-trace statement explicitly means the full perfect subcategory of D(A), not all bounded finite-cohomology complexes.

For step 2 I opened `thm-sf-ctf-stability`, `def-weil-finite-tor-amplitude`, and `prop-trf-compact-support-perfectness`. Stability clause (i) states exactly that pullback preserves D^b_ctf, and clause (iii) states ordinary direct-image preservation on the separated finite-type domain. Thus H=Lc_2^*K and Rc_2*H meet the perfectness theorem's input hypothesis on C and X respectively. No site-perfect or smooth hypothesis is added. Finite Tor amplitude is retained, as required when n>1. The proof uses neither the internal-Hom clause nor a numerical dimension bound.

For step 3 I read the same preservation and perfectness statements together with the constructible admissibility statement. Clause (v) applies to the specified constructible exceptional functor and gives J=Rc_1^!K in D^b_ctf(C,A); clause (iv) gives Rc_1!J in D^b_ctf(X,A). Perfectness therefore applies separately to J on C and Rc_1!J on X. No strong ambient adjoint, FullCD hypothesis or preservation assumption is substituted for this theorem. I read the corresponding current blueprint nodes for stability, admissibility, correspondence and compact-support perfectness; the same clauses occur there.

For step 4 I opened the current global-operator definition, compact-support direct-image definition and categorical-trace statement. The first explicitly provides the five arrows, proper-coincidence comparison and both compact-support composition comparisons, including their directions. The second defines the compact-support functor; I do not take composition or perfectness theorems from that definition. The categorical-trace node explicitly declares Perf(A) a full subcategory. Once steps 1–3 have proved all objects perfect, retaining those exact five ambient arrows and their composition is the elementary Hom-set argument written in step 4. The proof does not claim an extra functor isomorphism from a mere definition.

I copied the portions actually used from all cited node statements into citations.json, with an entry for each step/node pair. The statement of stability, not its proof, supplies all preservation assertions. The global-operator definition itself specifies the exact comparisons used. The excluded strong ambient admissibility citation has been removed. No uncited Stacks theorem, hidden source proof, renamed clause or new helper node is used.

I searched the whole DAG and blueprint for global-operator and perfect-complex statements with rg and tools/blueprint_refs.py. Naturality, triangulated compatibility and graph-operator nodes do not state this assertion, while the generic stability and compact-support-perfectness nodes already provide the needed results. Hence no new node or duplicate-tag pair is required, and blueprint.same_as is empty. The off-unit stability theorem is declared in split_report.tool_uses as a generic preservation tool: it does not replace the operator unit's route. The maintainer decides the accepted tool-use record.

I checked K=0, empty C, empty X and identity correspondence on Spec k. Empty C makes all four intermediate complexes zero; empty X forces empty C. For identity legs the conclusion reduces to the given endomorphism of a perfect coefficient complex. For n=1 the coefficient ring is a field; for n>1 the proof still uses finite Tor amplitude, never only finite cohomology. The coefficient conventions exclude n=0. No new statement needed separate edge-case testing.

The B–E review found no new-node form, duplicate or clause-renaming issue, and no change to the unit or chapter. The repairs in this pass were the invalid grep paths, repeated historical report sections, and the single long proof step; the earlier constructible-preservation repair was checked against the current source and retained. Only the designated sandbox was written.


## Second reading by Q90

I independently read delivery-errors B–E, the sandbox report and node, the current DAG statements of all ten distinct cited nodes, and the current main-20261015 statement and proof of this item. I compared the preservation clauses with `sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.md`, admissibility with `sec-six-functors-basics/sk-def-sf-admissible/def-trf-admissibility.md`, and perfectness and the trace category with `sec-smooth-purity/sk-prop-sf-trace-perfectness/`. The item statement matches the current blueprint hypothesis by hypothesis: the finite stage has n>=1 and ell different from p; the schemes are separated finite type; K is finite-Tor constructible; the exceptional leg has the specified constructible adjunction; the ordinary leg is proper. Its conclusion includes every intermediate object. The current source's appeal to strong ambient admissibility is stale; the split correctly uses the constructible theorem instead, without adding that false ambient condition.

- Step 1 — PASS against coefficient conventions, correspondence, constructible admissibility, proper-morphism definition, global-operator definition, compact-support perfectness and categorical-trace statements. I also read Stacks `morphisms.tex`, `definition-proper` (01W1), and `schemes.tex`, `definition-separated` (01KK). Properness supplies precisely separatedness and finite type of c_2; admissibility supplies these for c_1. The structure maps of X and C have the hypotheses of compact-support perfectness. The trace definition explicitly identifies the relevant D^b_fin with Perf(A).
- Step 2 — PASS against stability clauses (i) and (iii), the finite-Tor definition, and compact-support perfectness. Applying pullback to K gives H on C; applying ordinary direct image to H gives Rc_2*H on X. Both schemes and the morphism satisfy the stability domain. Perfectness applies separately to these two inputs. No site-perfectness, smoothness or numerical amplitude estimate is used.
- Step 3 — PASS against constructible admissibility, stability clauses (v) and (iv), and compact-support perfectness. The exceptional functor is the specified constructible one; its value J on C and Rc_1!J on X are finite-Tor constructible. These are exactly the exceptional-leg inputs appearing in the operator. No ambient adjoint assumption is used.
- Step 4 — PASS against the compact-support definition, the exact global-operator statement, and the full-subcategory clause of categorical trace. The operator definition explicitly supplies the unit, proper comparison, both composition comparisons and counit. The ordinary comparison goes from RΓ_c(X,Rc_2*H) to RΓ_c(C,H); the exceptional comparison goes from RΓ_c(C,J) to RΓ_c(X,Rc_1!J). The remaining argument is elementary: between perfect objects the full subcategory has the ambient Hom sets and composition, so the five given arrows and their composite remain in Perf(A).
- New nodes — NONE. B1–B7, duplicate-helper checks and new-node Mathlib-leaf conversion have no new nodes to inspect. The split uses the existing generic preservation and perfectness nodes and does not restate the item in a child.

For the small cases, K=0 makes all complexes and arrows zero; C empty makes all four intermediate objects zero; X empty forces C empty. On the identity correspondence of Spec k the assertion reduces to an endomorphism of the given perfect point complex. At n=1 the coefficient ring is a field; at n>1 finite Tor amplitude remains an essential input throughout. n=0 is outside the stated coefficient conventions. No statement dispute was found.

I checked all sixteen citations.json entries programmatically: every quote is a verbatim substring of the current cited node statement, and every proof-step citation has its entry. Reading the statements confirms that none is being used for a construction hidden only in its proof. The chapter and unit records and the current unit source retain the prescribed unit/proper-comparison/correspondence/composition/counit route. The declared off-unit stability tool supports that route rather than replacing it.

My independent attachment search found no occurrence of the item id in the slopmaster2 library or Comparator. I read `Correspondence.lean:808–869`: the three globalOperator definitions construct the composite under a geometric package and do not state this perfectness assertion. A fresh Mathlib LeanFinder search, using the more general phrasing “derived pullback and proper pushforward preserve bounded constructible complexes of finite Tor dimension”, returned underived sheaf composition and finite-limit results, cohomological-bound facts, and a generic exponentiable-morphism composition result, not this assertion. Its actual tool record is in searches.jsonl and mathlib_searches.

Changes in this second reading: appended this independent source-and-step review and the fresh preservation-search record. The proof, statement and sixteen valid citation quotations needed no repair and were retained.
