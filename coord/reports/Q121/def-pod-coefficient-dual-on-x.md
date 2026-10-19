# Worker report: def-pod-coefficient-dual-on-x

1. Files written: `dag/nodes/sec-six-functors/def-pod-coefficient-dual-on-x.json` (definition; split into existing statement dependencies; Mathlib has the generic closed-category construction, but not the full pro-etale/coefficient-stage item). No new nodes, no new Mathlib leaves. `citations.json` is the empty list because a definition has no proof steps.
2. Attachments: none. The previously rejected small-etale attachment is not proposed again.
3. WANTED: none.
4. The imported statement did not name its derived tensor, derived internal Hom, coefficient unit, or tensor–Hom adjunction directly. The source's final phrase named the canonical evaluation without spelling out which adjunction component it is. I added the existing definitions for these notions and expanded that phrase as the counit at the coefficient unit, equivalently the transpose of the identity. I used the current blueprint_update text (including “let”). The new wording has the same hypotheses and both displayed formulas as the source; this is an expansion of the definition, not a statement dispute. I removed the direct dependency on def-weil-geometric-hypotheses: the geometry is already supplied by the fixed setting, and no new geometric condition is used in the construction.
5. Unfinished work: none at this one-level split. The existing dependencies retain their own stage-1 status. No Lean was written, and no compiler, Lake, or build tool was run.

## Sources and search results

I read AGENTS.md, roles/worker.md, coord/brief-stage1.md, stages/1-dag.md, SETUP.md (including all three blueprint levels), GOAL.md, coord/dag-sync.md, tools/README.md, and coord/delivery-errors.md B–E. I read the sec-six-functors chapter record and the sk-thm-sf-package unit record, and the current main-20261015 package statement. This item is a component definition, not that unit's key theorem; it does not fill the unit's realization fields or replace its proof route.

The item's mathematical source is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/def-pod-coefficient-dual-on-x.md, both displayed formulas and its final tensor–internal-Hom-adjunction sentence. It is a definition and has no proof file or source proof to split into theorem steps. There are no newly created nodes requiring further sources or Stacks tags. No SGA source is used.

I searched the project source by the exact blueprint tag/id and by coefficientDual, derivedDual, derivedDualEval and coefficient dual. The etale coefficientDual/evaluation definitions have the rejected small-etale site. There are also genuinely pro-etale definitions AlgebraicGeometry.ProEtale.derivedDual in WeilConjectures/SixFunctors/ProEtale/Derived/Duality.lean:73 and derivedDualEval in Derived/Perfect.lean:126, with derivedDual_obj at :121 and derivedDualEval_eq_uncurry at :133. I read their surrounding category assumptions. I do not claim that these prove the item's entire four-stage adic/rational/common-stage coefficient interpretation, and I follow the explicit instruction to split rather than answer ATTACH again. The precise supplied stage-specific operations remain the DAG prerequisites, not an identification with discrete non-torsion etale sheaves or with arbitrary coefficient-valued sheaves.

The seven searches recorded in mathlib_searches were actually run with msearch.py and are in searches.jsonl. The first semantic phrasing found light condensed internal-Hom points and presheaf differentials, and LeanSearch found ordinary linear duals. A second semantic phrasing found CategoryTheory.ihom.ev. I read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:81–93 (adjunction and its counit), :144–151 (currying and uncurrying), :209–210 (uncurry_id_eq_ev), and :292–307 (internalHom and parameter adjunction). The generic evaluation is fully present in Mathlib. It assumes a given closed monoidal structure; these declarations do not construct the selected derived pro-etale/coefficient-stage operations. The separate grep in CategoryTheory/DerivedCategory found no derived dual/tensor/Hom/MonoidalClosed match. Consequently the whole item is split, with no invented Mathlib leaf for a different category.

I searched the whole DAG and blueprint with blueprint_refs.py search for “coefficient dual”, “evaluation”, and “tensor internal Hom”, and with key-word searches over dag/nodes. The existing sk-def-sf-operations statement explicitly contains the needed tensor–internal-Hom adjunction. Thus no new counit/evaluation lemma is needed. The general Hom definition is already supplied by the existing operation nodes. same_as is []: def-pod-conventions and sk-def-ops contain the coefficient-dual formula among other definitions, but do not state this complete definition including its evaluation; def-sf-pf also only defines the dual there; sk-def-pairing gives evaluation inside a pairing construction under an additional perfectness assumption. They are related existing material, not a second complete statement of this exact item.

## Not duplicates

No new nodes were created; there are no new/existing pairs to justify. In particular I did not turn the dual formula or the evaluation clause into its own new node, and did not create a generic adjunction lemma already present in Mathlib or the DAG.

## Review by Q121

I compared the final item with the current main-20261015 source, not just the older imported wording. Its two pieces of data are exactly RHom_X(K, Lambda_X) and evaluation K tensor^L K-dual -> Lambda_X. No assertion that K-dual is perfect, bounded constructible, or of finite Tor amplitude has been inserted. In particular this definition does not borrow the later coefficient-dual-perfect theorem and creates no backwards dependence on its own properties.

There are no proof steps: stages/1-dag.md section 3(2) requires a definition to be split by naming the notions it is built from. I therefore checked every statement dependency instead of fabricating proof steps for a definition. The statement of def-pod-conventions supplies the original fixed finite-field and coefficient data and explicitly says “On the small pro-etale site of X”. I preserve that fixed setting, including its imported admissibility convention; this item neither uses an ambient exceptional adjoint nor asserts that such an adjoint exists. def-weil-finite-tor-amplitude defines the precise D^b_ctf domain at the finite and integral stages and the rationalized/common-stage field conventions. def-weil-derived-pullback-tensor-hom supplies finite pro-etale tensor and internal Hom, the completed integral operations, and the rational/common-stage operations, rather than discrete non-torsion etale operations. sk-def-sf-operations (i) expressly states that K tensor^L - is left adjoint to RHom(K,-), naturally in K, in those coefficient conventions. I use its statement, not an inferred property from the name “internal Hom” or a fact hidden in its proof. Finally def-weil-ordinary-compact-cohomology expressly defines Lambda_Y as the finite constant sheaf, completed integral sheaf, or the prescribed field scalar extension. That statement justifies the stage-specific Lambda_X in the final text.

The types in the explicit adjunction bijection are correct: set the second adjunction argument to Lambda_X and the first to K-dual = RHom_X(K,Lambda_X). Its right-hand Hom then contains the identity of that very object. The inverse image is a map K tensor^L K-dual -> Lambda_X, in the source's order; no unnoticed tensor symmetry is needed. This is a construction from the cited adjunction, not a non-elementary theorem that needs a new node. It makes the source's canonical evaluation concrete and avoids an arbitrary choice of pairing. Mathlib's uncurry_id_eq_ev confirms the same convention.

I tested the definition on K = 0 (dual and evaluation are zero), K = Lambda_X (the dual is the unit and evaluation is the unit identification), and a finite free object or its shift (ordinary linear evaluation, with the usual derived shifts). The construction also makes sense for objects with finite Tor amplitude that are not assumed site-perfect: no dualizability or biduality is needed merely to form this counit. At the integral stage Lambda_X is completed, and at E and Qbar_ell it is the rational/common-stage unit, so the checks do not accidentally substitute a discrete non-torsion constant sheaf. Dimension zero and nonproper smooth schemes do not require any extra geometric input for this definition.

Against delivery-errors B–E: there are no new statement-only nodes to check, no clauses moved to relabelled nodes, no hidden non-elementary theorem in an elementary step, and no node cited for a claim its statement lacks. I checked the five dependency statements directly. The two candidate additions that would have conflated the generic condensed module layer with the selected adic coefficient category were avoided: the final split cites the already explicit stage-specific operation interface. A read-only dependency traversal shows the selected dependencies do not reach this item, so the new edges introduce no cycle. citations.json is correctly empty, proof_deps and proof remain empty, and the imported metadata and blueprint_update are retained.

## Earlier second reading (a previous round; superseded)

- Item statement: checked both displayed formulas, the fixed Poincare setting, and the current `main-20261015` blueprint update; verdict: faithful, with only the adjunction counit and its identity-transpose written explicitly.
- Statement dependency `def-pod-conventions`: checked the finite-field datum, smooth separated geometrically connected $X$, coefficient stages, small pro-etale site, and coefficient unit; verdict: supplies the fixed setting used.
- Statement dependency `def-weil-finite-tor-amplitude`: checked the finite-level, integral, rational, and common-stage meanings of $D^b_{ctf}$; verdict: supplies the domain without adding perfectness.
- Statement dependency `def-weil-derived-pullback-tensor-hom`: checked the stage-specific derived tensor and internal Hom constructions; verdict: supplies exactly the operations named in the definition.
- Statement dependency `sk-def-sf-operations`: checked clause (i)'s tensor--internal-Hom adjunction and its coefficient-stage typing; verdict: supplies the counit/evaluation construction.
- Statement dependency `def-weil-ordinary-compact-cohomology`: checked the definition of the finite, completed integral, rational, and common-stage coefficient unit; verdict: supplies the meaning of $\Lambda_X$.
- Proof steps: there are none because this is a definition; verdict: `proof`, `proof_deps`, and `citations.json` are correctly empty.
- New nodes: none; verdict: no duplicate, Mathlib leaf, source tag, or extra statement node was introduced.
- Small cases: checked $K=0$, $K=\Lambda_X$, finite free objects and shifts, dimension zero, and nonproper smooth schemes; verdict: the definition remains well-typed and makes no dualizability or properness claim.

I changed no node content during this second reading. I verified that the worker's explicit adjunction description is an unpacking of the source's canonical evaluation, that the added statement dependencies are existing definitions, and that no dependency is a restatement of the item or a hidden proof step. The delivery dry run is the remaining mechanical check.

## Resumed review by Q121 — 2026-10-17

I reopened the current main-20261015 item source and all five prerequisite statements during this resumed attempt. The fixed setting still specifies the small pro-etale site, and the finite-Tor definition distinguishes finite, completed integral, rationalized and common-stage coefficients. The operation definition supplies their respective tensor and internal Hom; clause (i) of sk-def-sf-operations explicitly supplies the adjunction in the order used by evaluation. The coefficient-object paragraph of def-weil-ordinary-compact-cohomology supplies the selected unit. Substituting that unit into this adjunction and transposing the identity has exactly the displayed source and target. This introduces no claim of dualizability or of constructibility preservation.

I reread the actual pro-etale derivedDual, derivedDual_obj, derivedDualEval and derivedDualEval_eq_uncurry declarations, including their coefficient-category assumptions. These concern derived categories of sheaves valued in a given abelian monoidal category; they do not identify the normalized integral, rationalized and common-stage categories in this item. The etale declarations use the wrong site. Thus no complete exact attachment is certified here. I also reread Mathlib's ihom.adjunction, ihom.ev and uncurry_id_eq_ev: the abstract counit exists there, while the selected coefficient-stage constructions remain the existing DAG dependencies.

The saved seven query/tool pairs all occur in searches.jsonl, and no searches were invented or newly asserted. Repeated whole-blueprint and DAG searches found related coefficient-dual definitions without a second complete statement of this item. A read-only traversal from each selected prerequisite found no path back to the item. The item remains a definition with no proof steps or new nodes, so citations.json stays empty. The zero object, the unit, finite free objects and their shifts give the expected evaluation, and no properness or perfectness hypothesis is introduced. No node changes were needed on this resumption. The required --no-push dry run was restarted; its result is recorded below once it finishes.


## Earlier second reading (a previous round; superseded)

- Item statement: compared hypothesis by hypothesis with main-20261015/sec-six-functors/sk-thm-sf-package/def-pod-coefficient-dual-on-x.md (order 2589), both formulas and the final adjunction sentence; PASS. The fixed setting and domain are retained, and the counit description only specifies the canonical evaluation already named by the source.
- Dependency def-pod-conventions: opened its full statement, including the finite-field data, smooth separated finite-type geometrically connected X, dimension d >= 0, nonproper allowance, admissibility convention and four coefficient stages on the small pro-etale site; PASS. Removing the direct geometric-hypotheses edge loses no datum because conventions already depends on it.
- Dependency def-weil-finite-tor-amplitude: opened the finite-level additional Tor condition, the uniform integral reduction interval, and both field-stage definitions; PASS. The item does not replace these by dualizability.
- Dependency def-weil-derived-pullback-tensor-hom: opened the finite ambient operations, integral completed tensor/internal Hom and the rational/common-stage constructions and their stated domains; PASS. Evaluation uses those operations and does not assert a new preservation theorem.
- Dependency sk-def-sf-operations, clause (i): opened the adjunction K tensor - left adjoint to RHom(K,-); PASS. Put the target equal to Lambda_X and the variable object equal to K-dual. The right-hand Hom is End(K-dual), so the identity has exactly the displayed inverse image. No exceptional-adjoint claim or proof hidden inside another node is used.
- Dependency def-weil-ordinary-compact-cohomology: opened its coefficient-object paragraph; PASS. It supplies the constant finite unit, completed integral unit and rational/common-stage coefficient objects named in the item.
- Proof steps: none, as required for a definition by stages/1-dag.md section 3(2); PASS. proof, proof_deps and citations.json are empty. No theorem has been relabelled as a new prerequisite.
- New nodes: none; PASS. Whole-blueprint searches for coefficient dual and tensor internal Hom and direct readings of def-pod-conventions, sk-def-ops, def-sf-pf and sk-def-pairing confirm the related definitions do not give this complete evaluation definition under precisely this domain.
- Mathlib/Lean audit: independently searched LeanFinder with the new query recorded below and read ihom.adjunction, ihom.ev, curry, uncurry and uncurry_id_eq_ev in Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:81-93,144-151,209-210; PASS for the generic construction only. Read pro-etale derivedDual (Duality.lean:73) and derivedDual_obj, derivedDualEval, derivedDualEval_eq_uncurry (Perfect.lean:121,126,133), including category assumptions; these do not identify the item's adic and common-stage categories. No exact attachment is claimed.
- Edge cases: K=0 gives the zero pairing; over a geometric point with field coefficients a finite-dimensional vector space gives ordinary evaluation, and K=Lambda_X gives the unit evaluation; n=1 is the residue-field case, while n=0 is excluded by the fixed setting; dimension zero introduces no extra condition. The empty scheme is outside the intended geometrically connected setting, but the same zero-category formula still makes sense. PASS: no perfectness or properness hypothesis was introduced.

Changes: retained the mathematical statement and dependencies, which passed the reading. Added one independently run Mathlib search to mathlib_searches, keeping searches.jsonl as emitted by msearch.py, and appended this explicit second-reading record. There are no proof citations to add. The first worker's Review by Q121 and all earlier report sections are preserved.


## Earlier second reading (a previous round; superseded)

- Item statement: read main-20261015/sec-six-functors/sk-thm-sf-package/def-pod-coefficient-dual-on-x.md, order 2589, including both formulas and its final adjunction sentence; PASS. The fixed setting, all four coefficient stages and arbitrary K in D^b_ctf are retained; no perfectness, properness or preservation conclusion is added.
- Dependency def-pod-conventions: read its complete statement; PASS for the finite-field and coefficient data, smooth separated geometrically connected finite-type X, dimension d >= 0, the small pro-etale site and the imported admissibility convention. Its indirect geometric-hypotheses dependency retains the removed direct edge's information.
- Dependency def-weil-finite-tor-amplitude: read its complete statement; PASS for the finite-level condition, uniform integral reduction interval and rational/common-stage categories. In particular bounded constructibility alone is not substituted for the finite-level Tor condition.
- Dependency def-weil-derived-pullback-tensor-hom: read its complete statement; PASS for finite ambient operations, completed integral operations and rational/common-stage constructions. Its constructible internal-Hom restrictions are not a preservation theorem; the present definition uses the operation interface and adjunction explicitly supplied by sk-def-sf-operations (i), and makes no additional stability claim.
- Dependency sk-def-sf-operations (i): read the ambient tensor/internal-Hom statement and its explicit adjunction; PASS. Fix K, put the target equal to Lambda_X and the variable object equal to RHom(K,Lambda_X). The right Hom is its endomorphism set, so transposing its identity gives exactly K tensor K-dual -> Lambda_X, without reversing tensor factors.
- Dependency def-weil-ordinary-compact-cohomology: read its coefficient-object paragraph; PASS for the finite constant, completed integral and rational/common-stage Lambda_X. No discrete non-torsion constant coefficient object is substituted.
- Proof steps: none; PASS against stages/1-dag.md section 3(2), because this item is a definition. Its proof and proof_deps are empty, and citations.json is correctly the empty list.
- New nodes: none; PASS. Opened the existing def-sf-coefficient-duality (point/module duality), sk-def-ops and def-sf-pf (dual formula without this complete evaluation definition), and sk-def-pairing (evaluation for perfect K). None requires a new node or replacement of the arbitrary-K definition by its perfect special case.
- Mathlib/Lean check: independently ran msearch.py loogle with CategoryTheory.ihom.ev and read Basic.lean:81-93,144-151,209-210; PASS for the generic counit and identity-transpose conventions. Reopened ProEtale/Derived/Duality.lean:73 and Perfect.lean:121,126,133, including coefficient-category assumptions; these do not identify all four selected coefficient-stage interpretations, so no exact full-item attachment or Mathlib leaf is asserted.
- Edge cases and dependencies: K=0 gives the zero pairing; K=Lambda_X gives the unit evaluation; over a point finite free modules give ordinary evaluation, and shifts pair opposite degrees. The n=1 residue-field case is allowed; n=0 is excluded by the fixed setting. The empty scheme formula is still well-typed if considered separately, and d=0 or a nonproper smooth X introduces no new hypothesis. Read-only traversal of statement and proof dependencies from all five prerequisites finds no path back to the item; PASS.

Changes: retained the mathematical statement and dependencies after checking them directly. Recorded the independently executed Loogle query, whose raw result remains in searches.jsonl, and added this section with the exact required heading. All first-worker sections, including Review by Q121, remain intact. No new nodes or proof citations were needed.

## Revalidation after returned delivery — 2026-10-17

The landing return identified one stale citation: `def-pod-conventions` had
changed after the earlier review. I reopened the current DAG file
`dag/nodes/sec-six-functors/def-pod-conventions.json` in the shared repository
and compared its whole statement with this item's use. The current statement
still supplies, in one fixed setting, the finite-field datum, smooth separated
geometrically connected finite-type $X$ and its dimension, exceptional-adjoint
admissibility, all four coefficient stages, the small pro-etale site, and the
stage-specific categories and operations. It now also records the coefficient
and Verdier dual conventions, Frobenius data, twists, and canonical purity
orientation. These added clauses do not alter the citation: this item takes
only the fixed setting and coefficient-stage meaning from that node, while its
separate dependencies supply the finite-Tor domain, tensor/internal-Hom
operations, adjunction, and coefficient unit. The current node therefore says
every fact used by the item's opening phrase and introduces no hypothesis that
the item omits.

I checked the other four statement dependencies again against their current
repository files and found no changes affecting this split. The item remains a
definition with no proof steps, no new nodes, and no citation entries in
`citations.json`; the existing dependency edge to `def-pod-conventions` is
retained because the item explicitly refers to that fixed setting. No cycle or
duplicate is introduced by the updated convention statement.

## Second reading by Q121

- Item statement: compared the sandbox node with the current `main-20261015` source file `def-pod-coefficient-dual-on-x.md`, including both displayed formulas and the tensor--internal-Hom evaluation clause; verdict: PASS. The expanded references only make the source's fixed setting, coefficient stages, finite-Tor domain, operations, and unit explicit, and add no perfectness, properness, or preservation claim.
- Statement dependency `def-pod-conventions`: read the complete current statement in `dag/nodes/sec-six-functors/def-pod-conventions.json`; verdict: PASS. It supplies the fixed finite-field/geometric setting, the small pro-etale site, four coefficient stages, and the coefficient-dual conventions used by the opening phrase.
- Statement dependency `def-weil-finite-tor-amplitude`: read its current statement; verdict: PASS. It supplies the finite-Tor meanings of $D^b_{ctf}(X,\\Lambda)$ at the finite, integral, rational, and common stages without adding dualizability.
- Statement dependency `def-weil-derived-pullback-tensor-hom`: read its current statement; verdict: PASS. It supplies the stage-specific derived tensor and internal-Hom operations named in the definition.
- Statement dependency `sk-def-sf-operations`: read clause (i) and its typed adjunction; verdict: PASS. Substituting $K^\\vee=R\\mathcal Hom_X(K,\\Lambda_X)$ and the target $\\Lambda_X$ gives the stated counit and identity-transpose map, with the factors in the displayed order.
- Statement dependency `def-weil-ordinary-compact-cohomology`: read its current coefficient-object paragraph; verdict: PASS. It supplies the finite constant, completed integral, rational, and common-stage interpretations of $\\Lambda_X$.
- Proof steps: none, because this is a definition; verdict: PASS under stages/1-dag.md section 3(2). `proof`, `proof_deps`, and `citations.json` are empty, so no uncited proof fact is hidden.
- New nodes: none; verdict: PASS. There are no statement-only nodes to check for B1--B7, no duplicate or restated node, and no Mathlib leaf requiring a declaration/file/line record.
- Small cases: checked $K=0$, $K=\\Lambda_X$, finite free objects and shifts, dimension zero, and the nonproper case; verdict: PASS. The formulas remain typed and impose no unmentioned properness or dualizability hypothesis.

Changes made in this second reading: added this required explicit review section only. No node statement, dependency edge, citation, or search record required repair; all prior worker and review sections remain intact.
