# Stage-1 report: det-def-sfb-module-pushforward-pullback

## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-module-pushforward-pullback.json`: definition, split using existing nodes; not a Mathlib leaf. Statement and statement dependencies are byte-identical to live. Five short proof steps replace the imported paragraph; the source path, search evidence, blueprint same_as and split_report are supplied.
- `citations.json`: ten verbatim statement excerpts, one for every step/node pair.
- `searches.jsonl`: six searches actually run by msearch.py for this item, retained verbatim with their tool-generated results and timestamps. No inherited searches are presented as mine.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaf used: `def-sfb-module-upper-star-comp`.

## Attachments

None. I searched the supplied `lean/WeilConjectures/` by the blueprint tag, CondensedRing namespace and the listed lowerStar/upperStar/adjunction/composition names. References occur, but the advertised general CondensedRing declarations are absent. The earlier attachment rejection supplied by the dispatcher is respected; the adic specialization does not cover arbitrary commutative condensed rings. Existing stale lean_audit records on other nodes are not used as proof evidence and are not changed.

## WANTED

None. This one-level split uses existing DAG statements for every non-elementary assertion.

## Sources and route

Read `GOAL.md`, the worker/stage-1 brief and stage contract, SETUP's three levels and tool rules, delivery-errors B--E (including the duplicated historical copy), the chapter record and the assigned unit record. The requested abandoned-directory glob returned no matching directories in any group. The active sandbox had only dispatcher `.brief*` markers, no item, report or search log. I copied the live item once and worked only on that copy. The prior attachment failure is evidence from the dispatcher prompt, not a search of my own.

The item source read is the latest blueprint snapshot `main-20261026` (via `literature/blueprint/latest/`), files:

- `blueprint/sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/det-def-sfb-module-pushforward-pullback.md`, complete statement;
- the adjacent `.proof.md`, complete paragraph;
- the current unit's `_section.md`, "Open--closed operations on module sheaves".

The live statement agrees with the latest source after whitespace normalization. The item has exactly the general coefficient-ring scope of its source, including Qbar_l as an instance; no prime, torsion, finite-type, flatness or qcqs condition is added. The constructions here are the prerequisite module operations, before the open--closed unit specializes them. No SGA source is used.

The stored `dag/units/sk-prop-sf-open-closed-triangle.json` is an older record in sec-smooth-purity, describing an etale distinguished triangle, whereas the current blueprint path has the pro-etale module-sheaf open--closed operations unit in sec-proetale-coefficients. This is an inherited unit-record discrepancy, not an error in the module construction. I preserve the assigned chapter/unit and do not edit the unit: this item is not its key proposition and cannot realize the whole triangle. The server review reports the existing empty realization as an advisory. The generic tool uses of `lem-sfb-pushforward-comp-monoidal` and `lem-sfb-eta-comp` are declared in split_report, as the current item proof explicitly calls for them.

## Mathlib search decision

All six searches in the node exactly reproduce the tool/query pairs run through msearch.py; all services were available. The first phrasing sought the full condensed-coefficient pro-etale construction. A second phrasing sought a general monoidal-adjunction lift with scalar change. LeanFinder and LeanSearch returned SheafOfModules/PresheafOfModules operations and ordinary ModuleCat/Rep scalar adjunctions. Loogle returned `SheafOfModules.conjugateEquiv_pullbackComp_inv`.

I read Mathlib's `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean` lines 32--49 and 139--145, and `PullbackContinuous.lean` lines 43--61 and 77--109. These use sectionwise module sheaves and construct a left adjoint through presheaf pullback/sheafification. They do not assert agreement with the specified internal module-object mapMod/Ext construction, so the whole item is not a one-line specialization. The generic search also found the explicit mapMod TODO at `CategoryTheory/Monoidal/Mon.lean:856`; `Monoidal/Internal/Module.lean` is about internal monoids in ordinary ModuleCat and algebras, not the module transport in this item. The already-existing leaf for the uniqueness-of-left-adjoints composition comparison is reused, not recreated.

## Not duplicates

No new-node/existing-node pairs are introduced.

`det-def-sfb-module-pushforward-pullback` vs `sk-def-sfb-module-pushforward-pullback`: these imported blueprint entries have the same construction and clauses, with det versus sk references for the underlying notions. I record the older blueprint entry in same_as; I do not create a third node or edit/merge another worker's node. The five existing module-operation definition nodes and the two existing compatibility lemmas already give the desired finer statements.

## Review by NG

I read the current source statement and entire proof paragraph, then opened all seven original proof-cited nodes and read their statements in full. I also read the det coefficient-morphisms and change-of-scalars statements used in the expanded steps, and compared the det/sk coefficient, module-object, transport and scalar-change definitions. Both presentations use the same sheafified tensor, the same p_X^* = pi_X^* p^*, and the forward coefficient maps; no unidentified replacement of coefficient categories is made.

Step 1 uses `def-sfb-module-lower-star` for the actual transport/restriction definition, underlying action, additivity and left exactness, and `def-sfb-module-upper-star` for the actual transport/extension definition and relative-tensor formula. Both statements explicitly allow an arbitrary commutative condensed ring and arbitrary scheme morphism, exactly the hypotheses here. This is an application of existing construction nodes, not a new node restating a clause.

Step 2 uses `def-sfb-module-upper-lower-adjunction`. Its statement supplies the lifted monoidal adjunction composed with extension/restriction, the identification of its right adjoint with the module pushforward, and the full natural Hom bijection quoted in the step. `det-def-sfb-coefficient-morphisms` explicitly states eta_f as the unit followed by f_*(alpha_f), so it supplies the mate relation rather than merely defining unrelated coefficient notation. The coefficient rings and module categories in the child nodes agree with those fixed here.

Step 3 uses `def-sfb-module-lower-star-comp` for the natural module isomorphism and its specified underlying abelian-sheaf comparison. `lem-sfb-pushforward-comp-monoidal` explicitly includes A=Ab among its instances and states monoidality of the very rebracketing comparison used here. `lem-sfb-eta-comp` states precisely eta_gf = c_(Lambda_X) g_*(eta_f) eta_g. I checked its canonical normalization: the pullback comparison is conjugate to the inverse of c, and alpha_h is the inverse pullback-composition comparison evaluated at p^*Lambda. The det pullback-from-point composition and coefficient-morphisms statements use this same convention. Thus no arbitrary alpha or eta is substituted into a lemma about canonical ones. No new compatibility lemma is hidden in the word "transport": the complete linear composition result is already the statement of the existing lower-star-comp node.

Step 4 uses `def-sfb-module-upper-star-comp`. Its statement gives the unique comparison whose forward mate is c, and identifies the inverse mate with c^{-1}. I explicitly preserve that direction, avoiding the historical reversed-mate error. The adjunction and pushforward comparison needed by that statement were obtained in steps 2 and 3.

Step 5 is an elementary inspection of the forward scalar-extension coequalizer in clause 2 of `det-def-sfb-change-of-scalars` and the coefficient-isomorphism assertion in `det-def-sfb-coefficient-morphisms`. Neither formula asks for a chosen inverse. It does not claim exactness of scalar extension for an arbitrary ring map. This keeps the source's distinction between definitions and later exactness arguments.

I checked small cases: f=id and g=id give identity functors/comparisons up to the specified adjunction isomorphisms; the zero coefficient ring gives the trivial module category without an excluded hypothesis; the zero module is sent to zero by the additive constructions; arbitrary nonflat ordinary scalar maps still define extension/restriction and their adjunction, so no flatness is smuggled into the construction. Empty schemes are allowed by the cited arbitrary-scheme statements. None of the steps assumes geometric points or conservativity on the pro-etale site.

Against B1--B10: no new nodes need self-contained statements, leaf declarations or fresh blueprint ancestry; the item preserves TeX and imported metadata; searches are authentic; the only same-content blueprint item is recorded; no unsupported Lean attachment is made. Against C1--C8: each non-elementary claim is the actual statement of a cited existing node, every citation has a verbatim excerpt, the proof-dependency list is the union of step uses, and the two generic off-unit compatibility uses are declared for maintainer review. Against D1--D5: no new restatement nodes, no wholesale proof relocation, no circular induction, and the source's proof is fully assembled from its named existing results. Against E1--E7: hypotheses, coefficient presentation, scalar-map direction and mate direction have been checked as above; there is no identified mathematical source error. Each step is below 800 characters, so no long step hides a new lemma.

Corrections made: replaced the imported paragraph by explicit, separately cited applications; corrected proof_origin.document from the statement file to its actual adjacent proof file; supplied genuine Mathlib searches; populated same_as and split_report. The statement, stmt_deps, import_flags and all imported blueprint_* fields remain unchanged. Only the item node is delivered.

## Verification

Server-only check_dag passed with no sandbox-introduced finding. Server-only review_split passed after split_report was supplied, with zero new nodes and only the inherited unit-realization advisory. The complete deliver.py dry run and push are performed after this report.

## Unfinished work

None for this one-level split. The existing nodes retain their own stage state; this delivery does not claim their historical Lean audit entries establish a proof in the supplied source.
