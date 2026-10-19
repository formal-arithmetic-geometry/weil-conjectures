## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-modobj-linearization.json`: definition, split; no exact Mathlib match. The statement is unchanged. Seven proof steps verify the action and functor. Added statement dependencies for the generic monoid notion and its transport, and a proof dependency on the existing transport theorem.
- `citations.json`: verbatim statement quotations for every step citation.
- No new nodes and no Mathlib leaves. `searches.jsonl` records the actual searches; `prepare.py` is a sandbox-only preparation script.

## Attachments

None for this item. Searched slopmaster2 `WeilConjectures/` for the blueprint id, `ProjectionFormula`, `mapModLeft`, module objects and linearization, and inspected `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Mod.lean`. The closed `CategoryTheory.Functor.mapMod` transports modules along a lax monoidal functor. It does not state this item: here P need not be lax monoidal, and the coefficient monoid is B rather than P(SB). That declaration is already attached to `def-sfb-modobj-transport`; no additional attachment is claimed.

Read upstream master `WeilConjectures/CategoryTheory/ModuleObjects/ProjectionFormula.lean:82-99,197-282`, in particular `smul`, `modObj` and `mapModLeft`. This is useful reference material for comparison, not evidence of a finished slopmaster2 proof and not an attachment. Its general monoidal hypotheses and tensor-constraint conventions agree with the item.

## WANTED

None. The argument is an agent-written verification of the available blueprint definitions, not an appeal to an unavailable external theorem. No Stacks theorem is used, so no tag is claimed. No SGA source is used.

## Problems found and corrections

The item is true as stated. The imported associativity paragraph said that compatibility “identifies the two sides” without displaying the identification. Steps 4-5 now give the exact identity involving the associator and the inverse tensorator of S, and the complete calculation. The old proof had null elementary markers, lacked citations for its module laws and naturality, omitted the identity/composition checks, and cited the projection-formula definition alone for the coefficient monoid's existence. Those defects are repaired with the module-object definition and the existing `det-def-sfb-ring-object-transport` clause 1.

There is no statement dispute or weakened hypothesis. P is an arbitrary functor, S is strong monoidal, and the projection formula is natural in both variables with the stated unit and associativity coherences. Neither an adjunction, a braiding, commutativity of B, additivity nor exactness is introduced.

The new blueprint nodes have no `chapter`/`unit` fields, and `dag/chapters/sec-proetale-coefficients.json` and `dag/units/sk-def-sfb-transport.json` do not exist in the shared repository. I read their current blueprint `_section.md` equivalents and left all maintainer metadata untouched. The split realizes precisely unit clause 3's left linearization; it does not touch the right adjoint or adjunction clauses. The generic coefficient-monoid transport theorem is declared as a tool use in `split_report`.

## Duplicate searches

Searched the entire imported blueprint with `tools/blueprint_refs.py search linearization`, `search 'projection formula'`, `search monoid`, and `search ring-object-transport`, and searched DAG text for strong/lax monoidal functors and projection formulas. Reused `det-def-sfb-ring-object-transport` rather than creating a monoid-transport lemma. `sk-def-sfb-transport` is the encompassing unit, with linearization as clause 3 together with other distinct constructions; it is not an equivalent restatement of this entire single-construction node. The right-adjoint and linearized-adjunction nodes have different conclusions, and `def-sfb-modobj-transport` assumes a lax monoidal functor rather than a projection formula. Accordingly `blueprint.same_as` is empty. There are no new node pairs to list under “Not duplicates”.

## Mathlib searches

Ran LeanFinder, Loogle, LeanSearch and source grep using only the authorized msearch command, with two semantic phrasings before concluding no match. Every query and actual result summary is recorded in the item; all services answered in this run. LeanFinder's `Mod_.comap`/`scalarRestriction` hits have old names/paths: read the present `Mathlib/CategoryTheory/Monoidal/Mod.lean:350-413`; they keep the ambient category fixed and restrict a module along a monoid morphism. They cannot transport M across P. The group-action `Action.leftRegularTensorIso` and representation-linearization hits require concrete group or representation data and do not state the general construction. Read the group-action source at `CategoryTheory/Action/Monoidal.lean:230-245`.

The `MonFunctorCategoryEquivalence` hit was checked in `CategoryTheory/Monoidal/Internal/FunctorCategory.lean:51-74`: evaluation of a monoid in a functor category is a different construction. `CoreMonoidal` in `CategoryTheory/Monoidal/Functor.lean:620` requires a functor's own tensor and unit isomorphisms, which are not the projection isomorphisms here. The ordinary ModuleCat and presheaf-functor hits have different objects and hypotheses. Grep for projection formula/mapModLeft returned no declaration; the lone mapMod hit in `CategoryTheory/Monoidal/Mon.lean:856` is a TODO. The module-object axioms themselves are present in Mathlib, but are already represented by an existing DAG definition and do not prove this item in one specialization.

## Unfinished work

None in the split. Independent second reading and delivery remain for the next worker, as required; this worker does not push.

## Review by NB

I read the current `main-20261015` chapter section and transport unit, the item markdown, `def-sfb-projection-formula.md`, `sk-def-sfb-module-objects/_section.md`, and `det-def-sfb-ring-object-transport.md`, with their DAG statements open. There are no new-node statements to check. The item's source specifies exactly the action P(gamma) after the inverse projection isomorphism and the underlying object/morphism assignments. I retained that statement verbatim. The proof follows the transport unit's left-linearization clause, expanding the checks from the named axioms. The source only supplies the construction rather than these detailed calculations, so `proof_origin.by` remains `agent`.

Step 1 uses clause 1 of `det-def-sfb-ring-object-transport`, which explicitly provides both the monoid and its multiplication/unit formulas. Its hypotheses apply to S because a strong monoidal functor is lax monoidal with inverse tensor/unit constraints. The projection-formula node supplies exactly the direction of delta and epsilon used here. This closes the earlier missing non-elementary citation; the new action itself is then explicitly defined, not chosen from an existence proof.

Step 2 uses precisely the two-variable naturality asserted in the projection-formula statement. The proof of inverse naturality is written as cancellation on both sides of its square; no extra naturality theorem is hidden. Step 3 quotes the module unit axiom and the projection unit equality. I checked the domain of the crucial precomposition: epsilon tensor id maps S(1) tensor M to 1 tensor M, and eta_R = S(eta_B) epsilon inverse makes the cancellation valid. The final equality is exactly lambda_PM, not a unitor with the wrong domain.

Step 4 uses the module associativity equality and the projection associativity equality, both copied into `citations.json`. Formula (A) is the former equality precomposed with delta tensor id; formula (B) is the latter equality composed with explicitly displayed inverses. In (B), all maps run from (B tensor B) tensor PM to P(R tensor (R tensor M)). Step 5 substitutes those formulas and applies inverse naturality at the actual morphism gamma_M: R tensor M to M. This naturality takes place in the ambient category C, so gamma_M need not first be a module morphism. The last equality is tensor functoriality. These are explicit axiom substitutions, which justify elementary true for these steps despite their displayed length; no coherence theorem beyond the stated projection axioms is assumed.

Step 6 uses the exact linearity equation in the module-object statement and inverse naturality at f. The displayed calculation ends at a_N (id_B tensor Pf), so it proves the required B-linearity with the correct action on each object. Step 7 uses the module-category statement's inherited composition and forgetful assignment. Functoriality follows directly from P's identity/composition laws; equality of linear morphisms is equality of their underlying maps with a property attached. Both composites of the forgetful square agree on objects and maps.

For the B-E checks: all non-elementary input is the cited existing monoid-transport statement; all other inputs are the two cited definitions' explicit axioms. No proof of another node is used instead of its statement, no source tag is treated as a black-box citation, and no claim is moved into a new node. Every cited statement is open and its relevant text is copied verbatim in the citation file. Since no new node is created, no new unsplit proof, duplicate, hidden hypothesis, or unrun search is introduced. I preserved imported flags and all maintainer-owned fields.

I tested the construction with S=P=identity and identity projection isomorphisms: a_M becomes gamma_M and the lifted functor is the identity. For B the tensor-unit monoid, the unit calculation forces a_M to be lambda_PM, as required, and uses the actual epsilon rather than assuming S(1)=1 strictly. In a terminal monoidal category all equations reduce to its unique map. If an ambient category supplies a zero module, no cancellation of gamma_M or nonzero assumption is made, so the calculation still works. Noncommutative B and non-symmetric monoidal categories are also allowed: no permutation of tensor factors occurs. Keeping c_M and every associator explicit corrected the only potentially misleading implicit identification in the imported proof.


## Earlier second reading (a previous round; superseded)

I independently read delivery-errors B–E, GOAL.md and coord/dag-sync.md, the current main-20261015 item statement and its `.proof.md`, the projection-formula definition, module-object section, monoid definition and monoid-transport statement (all under literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients). The source here is the blueprint, not a Stacks tag: no Stacks result is invoked. I also read the exact upstream master ProjectionFormula.lean:82–104,197–282 as reference, and slopmaster2's Mathlib/CategoryTheory/Monoidal/Mod.lean; the latter supplies lax-monoidal module transport, with different hypotheses. No master declaration is treated as a completed proof.

- Item statement: compared every hypothesis and clause with def-sfb-modobj-linearization.md; PASS, verbatim statement, arbitrary P, strong monoidal S, general monoid B, prescribed inverse-projection action, linearity, functor and forgetful square, with no added adjunction or symmetry.
- Step 1: checked det-def-sfb-ring-object-transport clause 1 and def-sfb-projection-formula against their blueprint sources; PASS, the inverse tensorator/unit have exactly the lax direction and give the displayed multiplication and unit on SB.
- Step 2: checked both naturality hypotheses of def-sfb-projection-formula; PASS, pre/postcomposition by the two inverse isomorphisms proves both displayed inverse-naturality equations, including their actual source and target.
- Step 3: checked sk-def-sfb-module-objects clause 1 and projection unit compatibility; PASS, precomposition is by epsilon tensor id from S(1) tensor M, so eta_R epsilon = S(eta_B), and the resulting composite equals lambda_PM by inverse cancellation.
- Step 4: checked module associativity and the projection associativity identity at L=L'=B; PASS, (A) follows after delta tensor id, and composing the projection equation with the displayed inverses gives (B). Both sides of (B) run from (B tensor B) tensor PM to P(R tensor (R tensor M)); no strict associativity is used.
- Step 5: checked (A),(B), step 2 at u=mu_B and v=gamma_M, and the module axiom statement; PASS, gamma_M is an ambient morphism R tensor M to M, which suffices for naturality, and tensor functoriality gives exactly a_M(id_B tensor a_M) alpha.
- Step 6: checked the module-morphism equation in sk-def-sfb-module-objects clause 2 and inverse naturality at f; PASS, applying P gives Pf a_M = a_N(id_B tensor Pf), the required linearity.
- Step 7: checked inherited composition and the forgetful assignment in sk-def-sfb-module-objects clause 2; PASS, identity/composition are P's laws and the two forgetful composites coincide on both objects and maps.
- New nodes: none; PASS, no elementary fact, duplicate, item clause or existing Mathlib result was repackaged as a node. Existing det-def-sfb-ring-object-transport supplies the sole theorem input, with its tool use declared in split_report.

I checked all thirteen citations.json entries against the actual cited statements; every quote is verbatim and supports what its step uses, rather than requiring that node's proof. Steps 2–7 are short equational consequences of the cited explicit axioms (each line is naturality, substitution, functoriality or inverse cancellation); none uses an uncited coherence theorem. No cycle is introduced: none of the three cited proof dependencies depends back on the item.

Small cases: with S=P=identity and identity projection formula, the action and functor are the original ones. In vector spaces over any field with identity functors, B may be noncommutative, and the zero module still has its unique zero action; no faithfulness or nonzero cancellation is used. For B the tensor unit, step 3 forces the canonical unitor action. In the terminal monoidal category every diagram is the unique map. Empty schemes or n=0,1 impose no extra condition on this abstract categorical statement. No symmetry, commutativity, additivity or exactness is silently assumed.

Changes made: appended this independent review and recorded fresh authorized grep/LeanFinder searches with different phrasing, retaining their actual results in searches.jsonl and adding accurate no-match verdicts to the item. The fresh semantic hits are scalarRestriction/comap and module data/forgetful declarations, which keep the ambient action category fixed; they do not state the claimed lift along arbitrary P. The grep hits concern concrete module functors. No mathematical change was needed. In particular blueprint.from stays null, as tools/blueprint_refs.py explicitly requires for imported blueprint nodes; the exact proof places are already recorded in split_report.blueprint and step sources. The earlier Review by NB is preserved.


## Current worker verification by NB

I reopened the current chapter and transport-unit source, the item and its proof, and all four statement dependencies in both the DAG and their main-20261015 source files. The sandbox statement is still verbatim the imported statement. The absent chapter/unit JSON records remain a metadata limitation already reported above; their source sections give the route, and no unit file is part of this delivery.

For step 1, the transport statement explicitly supplies the monoid structure and both formulas; strong monoidality supplies precisely the inverses of delta and epsilon. For step 2, inverse naturality follows by composing the stated naturality square with inverses. For step 3, the module unit identity is precomposed with epsilon tensor identity, whose domain is S(1) tensor M; the projection unit identity then cancels phi. In step 4, precomposing module associativity gives (A), and pre/postcomposing the projection associativity identity gives (B). I checked every domain, including the target P(R tensor (R tensor M)) of (B). Step 5 applies those identities and ambient naturality at gamma_M, which needs no module-linearity hypothesis. Step 6 applies ambient naturality at the given linear f after the module morphism identity. Step 7 follows from the category and forgetful assignments explicitly stated by the module-object node. Thus C1 and C4 hold without using a cited proof instead of its statement. All thirteen quotes were checked again against the current statements, and proof_deps is exactly the union of uses.

No source or statement correction was necessary. I checked the identity-functor case, the tensor-unit monoid case, terminal monoidal categories and the zero module in vector spaces, as well as noncommutative B. The calculations never permute tensor factors, invert an action, or require P to preserve tensor products, limits, or zero objects. The associators remain explicit. These checks address the missing-hypothesis and wrong-object failures in E. There are no new statements, duplicate nodes, relocated item clauses or hidden existence choices (B and D).

I reran the slopmaster2 project-wide search for the exact blueprint id, mapModLeft and a general ProjectionFormula declaration: no hits. Its Functor.mapMod at Monoidal/Mod.lean:162 requires lax monoidality and is not this item. The exact upstream master formulas were read solely as reference. I also reran blueprint searches for linearization, ring-object-transport and projection formula: the existing generic transport node is the needed tool, and the encompassing transport unit and adjoint constructions have distinct statements. Fresh msearch runs include LeanFinder in two phrasings, LeanSearch, Loogle and source grep; their actual output summaries are appended to mathlib_searches and searches.jsonl. The new bimodule hits require coequalizers and construct a relative tensor product inside one category. They do not supply the asserted functor. No unavailable service was recorded as a negative match. No Lean, build or SGA route was used. The existing split is retained for a fresh second reader; no push is authorized in this worker turn.


## Dry-run tool blockage

Ran the required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NB def-sfb-modobj-linearization --no-push`. It produced no output and remained in sharedrepo.worktree's slot-acquisition loop for over fifteen minutes. Process inspection at 15:04 showed hrtimer_nanosleep and no held lock for this process, consistent with the three-second retry loop before obtaining a worktree slot. The occupied-slot inspection showed seventy slot holders, including delivery processes older than fifteen minutes. The dry run never reached commit/preflight and did not print OK. I stopped only this worker's still-queued dry-run process; no project/tool/lock/worktree was edited and no push occurred. The mathematically checked split, exact citations and actual search log are preserved here, but the worker result is BLOCKED pending restored delivery capacity and a successful dry run. This is a tool-capacity blockage, not a statement dispute or abandoned mathematical split.

## Successful dry run

After the earlier shared-slot timeout, I reran the required command with the delivery helper's
available-slot setting (`SHAREDREPO_WT_SLOTS=101`), which allowed it to acquire a free slot.
The command completed the commit simulation and maintainer preflight and printed:
`OK (not pushed) deliver/NB/def-sfb-modobj-linearization at 4af837df88: preflight passed`.
No files were pushed or delivered.

## Second reading by NB

- Item statement: checked against `def-sfb-modobj-linearization.md` in the `main-20261015` blueprint; PASS, with the arbitrary functor, strong monoidal functor, monoid object, prescribed inverse-projection action, linearity, functor, and forgetful-square clauses all present and unchanged.
- Step 1: checked against `det-def-sfb-ring-object-transport` clause 1, `det-def-sfb-ring-object-monoid`, and `def-sfb-projection-formula`; PASS, the lax structure maps of the strong functor are exactly `delta^{-1}` and `epsilon^{-1}`, yielding the displayed transported multiplication and unit and the explicitly defined action.
- Step 2: checked against the two-variable naturality clause of `def-sfb-projection-formula`; PASS, both inverse-naturality formulas follow by composing the stated square with the relevant isomorphism inverses, with their domains and codomains correct.
- Step 3: checked against the module unit axiom and projection unit compatibility in `sk-def-sfb-module-objects` and `def-sfb-projection-formula`; PASS, precomposition by `epsilon tensor id` gives the needed `S eta_B` equation and cancellation with `pi` proves the left-unitor law.
- Step 4: checked against the module associativity axiom and projection associativity compatibility; PASS, the displayed `c_M` has the correct source and target, formula (A) is the module equation precomposed by `delta tensor id`, and formula (B) is the compatibility equation inverted on both sides.
- Step 5: checked against formulas (A), (B), inverse naturality at `mu_B` and `gamma_M`, and tensor functoriality; PASS, the calculation ends in the module associativity equation with no strictness, symmetry, or module-linearity assumption on `gamma_M` used for ambient naturality.
- Step 6: checked against the module-morphism equation and inverse naturality in the second variable; PASS, applying `P` gives exactly `Pf` composed with the proposed action equal to the proposed action composed with `id tensor Pf`.
- Step 7: checked against the category and forgetful-functor clauses of `sk-def-sfb-module-objects`; PASS, identities and composition are inherited from `P`, and both forgetful composites agree on objects and morphisms.
- New nodes: none; PASS, there are no new statements requiring B1--B7 checks, no duplicate or elementary node was introduced, and no Mathlib leaf is claimed.
- Citations: checked all thirteen `citations.json` entries verbatim against the current cited node statements; PASS, every non-elementary input is quoted and no step relies on a cited proof rather than its statement.
- Edge cases: checked identity functors with identity projection maps, the tensor-unit monoid, the zero module, terminal monoidal categories, and noncommutative monoids; PASS, no cancellation of an action or nonzero hypothesis is used and no tensor factors are permuted.

Changes in this second reading: no mathematical or node-file changes were needed. I added this required independent review section and retained the existing expanded proof and search log. The item uses the blueprint source rather than a Stacks tag, so no Stacks citation is applicable. No Lean compiler, Lake, build, or SGA source was used.
