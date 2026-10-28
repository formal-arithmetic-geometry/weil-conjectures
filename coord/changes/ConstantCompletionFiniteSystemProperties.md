# CategoryTheory.ConstantCompletion.finiteSystem_properties
## Reason
The prior statement quantified over arbitrary `Module` instances and asserted the canonical scalar tower. That is false because module structures are not unique (terminal site, `I = 0`, `A = ℤ[X]`, regular action twisted by `X ↦ X + 1`). The repaired statement installs the canonical module structures induced by the quotient constant sheafification units.
## Old
`[∀ n U, Module (A ⧸ I ^ (n + 1)) (adicTerm J A (finiteSystemUnder J A I) n U)]` and the conjunction of scalar tower, flatness, surjectivity, and tensor reduction.
## New
A `letI` installs `finiteSystemModule J A I` (a new `@[instance_reducible]` definition in `Sheaf.Paper.ConstantCompletionFiniteSystemProperties`, owned by node `new-e2-constant-completion-finite-system-properties`), followed by the same four conclusions.
## Users
| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.ConstantCompletionFlatAndQuotientsProjection` | unclaimed | Forced adaptation: install `finiteSystemModule J A I` instead of `Classical.choice (finiteSystem_module_instances J A I)`, so that the module instances agree with the repaired theorem. |
| `Sheaf.Paper.ConstantCompletionProjectionKernel` | unclaimed | Forced adaptation: install `finiteSystemModule J A I` (a local `let`) before applying the repaired theorem, which no longer takes the instance from the local `quotientModule`. |

`CategoryTheory.ConstantCompletion.finiteSystem_module_instances` (Sheaf.Paper.ConstantCompletionFiniteSystemModules) is unchanged and now has no user.
## Status
landed 20261028T020622-L-2530190 2026-10-28 (merge of deliver/P4/Sheaf.Paper.ConstantCompletionFiniteSystemProperties)
