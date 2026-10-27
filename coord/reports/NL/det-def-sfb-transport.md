# Worker report: det-def-sfb-transport

## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-transport.json` — the item, changed from imported to split; no new nodes and no Mathlib leaves.
- `citations.json` — nine exact statement quotations covering all citations in the three proof steps.
- `searches.jsonl` — eight Mathlib searches executed for this item by the required search command.
- `report.md` — this report.

## Attachments

None. The earlier proposed attachment was rejected because `CategoryTheory.Adjunction.mapModAdjunction` is only the monoidal-adjunction clause, not the whole item. The live source has separate declarations for the component constructions, and no project declaration states all four clauses under the item’s hypotheses.

## WANTED

None. The current blueprint and all cited component-node sources are present locally. The historical unit binding is stale and is preserved without editing the unit record.

## What was wrong or incomplete

The imported item had paragraph-sized proof steps with no `source` fields, `status: imported`, and empty Mathlib searches. Its live `unit` field points to `sk-prop-sf-open-closed-triangle`, whose historical unit record is in the smooth-purity chapter and has an unrelated open–closed-triangle statement. I preserved this stale binding and did not modify the unit record, because assigning this item to that unit would introduce an invalid reachability finding. Its old proof also cited component nodes without recording the exact statements used. I retained the current statement and dependencies, added source locations for each assembly step, supplied the current blueprint ancestry, and set `status: split`. No statement dispute was found.

The prior attachment attempt treated `CategoryTheory.Adjunction.mapModAdjunction` as if it covered the whole item. Reading the live declarations shows that it proves only transport for a monoidal adjunction; the projection formula structure, both linearizations, and the projection-formula-specific adjunction are separate constructions. I therefore split the item by its three proof paragraphs and cite all nine existing component nodes directly. No new node is justified: each proposed subclaim already has a DAG node, and Mathlib does not state the full internal-monoid package.

## Not duplicates

No new nodes are delivered, so there are no new-node duplicate pairs. The nine cited nodes are the existing statements corresponding to the item’s clauses, not newly created restatements.

## Review by NL

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `roles/worker.md`, `SETUP.md`, `GOAL.md`, delivery-errors sections B–E, the current chapter record `dag/chapters/sec-proetale-coefficients.json`, and the live unit binding `sk-prop-sf-open-closed-triangle`. I inspected the archived-attempt path required by the brief; it had no matching abandoned directory. The active sandbox contained only dispatcher marker files, so I copied the live item and did not reuse an earlier proof. I read the current `literature/blueprint/latest` item and proof at `sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/det-def-sfb-transport.{md,proof.md}` and checked the blueprint ancestor query.

For Step 1, the cited `def-sfb-modobj-transport` statement explicitly gives the lax-monoidal action, linearity of mapped morphisms, the `mapMod(F)` functor, and commutation with forgetful functors. The cited `def-sfb-modobj-transport-adjunction` statement explicitly gives the unit morphism of monoids, restriction along that unit, and the adjunction `mapMod(F) ⊣ Res_u ∘ mapMod(G)`. These are exactly the two claims in clauses 1 and 2; no stronger monoidal or coefficient hypothesis is introduced.

For Step 2, I read `def-sfb-projection-formula`, which states the natural isomorphisms and unit/associativity coherence required of a projection formula. I read `def-sfb-modobj-linearization`, whose statement supplies the action through the inverse projection isomorphism and the functor `P_B`; `def-sfb-modobj-linearization-right-adjoint`, whose statement supplies the mate action and functor `G_B`; and `def-sfb-modobj-linearized-adjunction`, whose statement says the original adjunction restricts to `P_B ⊣ G_B`. Thus every clause of item part 3 is taken from a statement that actually contains it. The monoid object and module-object hypotheses are those named in the cited statements.

For Step 3, `def-sfb-adjunction-has-projection-formula` states the canonical projection-formula map as the adjoint of the displayed composite and defines the isomorphism condition. `def-sfb-adjunction-projection-formula` states that these maps form the projection formula from Step 2. Finally, `def-sfb-modobj-linearization-transport-adjunction` states `P_B ⊣ mapMod(S)` and the corresponding linear Hom correspondence. These statements jointly supply all assertions in item part 4, with the same adjunction and strong-monoidal hypotheses. The nine citation entries in `citations.json` were checked programmatically against the current live node statements; every quote is a literal substring.

I checked the live Lean source under `lean/WeilConjectures/CategoryTheory/ModuleObjects`: `MapMod.lean` contains `CategoryTheory.Adjunction.mapModAdjunction`, while `ProjectionFormula.lean` contains the separate projection formula and module constructions. This confirms why the former cannot attach the whole item. I searched the project source for the blueprint tag and all listed declarations and found no declaration tagged for the complete item. I also checked all nine cited DAG nodes for their current status and statements, and no citation points back to this item.

The required Mathlib searches were run twice with distinct semantic phrasings where useful. LeanFinder returned only `ModuleCat`/`Rep` special cases; LeanSearch returned monoid transport (`mapMon`) and tensor-Hom results; Loogle gave no match (including the recorded parser/unknown-identifier diagnostics); and Mathlib grep found only the TODO for `mapMod` in `Mathlib/CategoryTheory/Monoidal/Mon.lean`. I read the relevant returned declarations and recorded the exact executed queries and verdicts in `mathlib_searches` and `searches.jsonl`. Therefore the whole item is not a Mathlib leaf.

Small-case checks: with an identity lax monoidal functor, Step 1 reduces to the identity module transport; with an identity monoidal adjunction, Step 1’s restriction is along the identity monoid map; with `P` and `S` identity, the projection formula is the canonical unit/associativity family and the module adjunction is the identity adjunction. For a monoid object `B`, the source and target categories in Steps 2–3 are respectively `Mod_{S B}(C)` and `Mod_B(D)`, matching every cited statement. No clause is weakened and no extra commutativity, exactness, or existence assumption is smuggled in.

No Lean file was written and no compiler, Lake, build, or global-check command was run. The pre-report server `check_dag` returned `OK` for this sandbox.

## What I could not finish

Nothing required for this stage-1 split. The required server dry run passed (`OK (not pushed)` at receipt commit `0fb84d3e2f6`).
