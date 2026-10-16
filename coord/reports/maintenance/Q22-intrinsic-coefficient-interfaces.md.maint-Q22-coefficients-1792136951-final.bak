# Q22: stale intrinsic coefficient interfaces

The compact-support consumer was dispatched repeatedly because its coefficient dependencies had Lean module records, although those modules still used the old integral full subcategory after the owning integral record migrated to `Sheaf.Paper.SfIntegralConstructible`. The two completeness predicates and reduction functors are not definitionally interchangeable; no recorded canonical comparison supplies this missing interface. The bottom-up worker correctly refused to restate other genuine DAG nodes. Source readers worked.

This maintenance archives and clears the seven stale `lean` and `reviewed_lean` records, reopening their owning nodes for normal stage 2. Their statements, dependencies, proofs, stage-1 reviews and Lean source files are unchanged. No new mathematical node, definition, axiom or proof is supplied. Each node's `lean_invalidation` explains the precise repair and preserves its complete former interface and review. It is a historical record; a subsequent valid `lean` attachment closes the repair normally.

The `FiniteFieldDatum` binder in the legacy modules does not itself force Y to be a scheme over that finite field. The concrete obstruction is the different integral predicate and absent comparison, not that binder alone. Do not narrow the compact-support statement to finite fields. Keep existing legacy declarations for their callers and add the intrinsic interface in the owning node's module.

## Owning nodes to repair

- `lem-weil-integral-constructible-triangulated`: State triangulated and isomorphism closure for the currently recorded sfIntegralConstructible predicate, and expose the inherited structures on sfIntegralConstructibleCategory. The old theorem is about a different predicate.

- `lem-weil-integral-constructible-linear`: Retain the canonical constant-section action on the ambient category, and expose the linear category and linear shift on the currently recorded sfIntegralConstructibleCategory, using its repaired triangulation. The archived ambient theorem alone does not supply this full node's subcategory clause.

- `lem-weil-integral-scalar-extension-constructible`: State preservation of the currently recorded sfIntegralConstructible predicate by the existing integral scalar extension and expose its restricted functor between sfIntegralConstructibleCategory stages, with its stated linearity.

- `def-weil-rationalization-karoubi`: Specialize the existing generic ScalarLocalization to the currently recorded sfIntegralConstructibleCategory, with unchanged objects, the specified Hom localization, inherited triangulation and completed integral scalar transitions. The old boundedConstructibleDerivedCompleteIntegralCategory specialization is not the current dependency. Keep any global datum required by the source statement; it imposes no relation between Y and its finite field. Expose an interface usable over arbitrary schemes without an extra finite-field assumption.

- `lem-weil-scalar-extension-composition`: State the normalized tensor unit, composition and coherence for the repaired rationalization interface on intrinsic integral stages, retaining the canonical tensor characterization rather than an arbitrary natural isomorphism.

- `lem-weil-scalar-extension-exact-triangulated`: State shift compatibility and exactness for the repaired rational scalar extension between the intrinsic stages, using the repaired integral restriction.

- `def-weil-algebraically-closed-coefficients`: Specialize the existing common-stage pair construction to the repaired rational stages on sfIntegralConstructibleCategory and their normalized scalar transitions. Retain literal pairs, representative Hom colimits, the common-stage triangles, independent scheme/closure universes, and no Karoubi completion. Expose a usable intrinsic interface; do not reattach the old finite-stage category unchanged.


## Queue validation

Production `dag_queue.Dag.stage2()` reproduces consumer admission before the repair and rejects it afterward. The following replay uses only in-memory dummy module markers to verify dependency order, never to certify Lean work:

```json
{
  "consumer_eligible_before": true,
  "consumer_eligible_after": false,
  "repair_frontier": [
    "lem-weil-integral-constructible-triangulated",
    "lem-weil-integral-scalar-extension-constructible"
  ],
  "simulated_repair_waves": [
    [
      "lem-weil-integral-constructible-triangulated",
      "lem-weil-integral-scalar-extension-constructible"
    ],
    [
      "lem-weil-integral-constructible-linear"
    ],
    [
      "def-weil-rationalization-karoubi"
    ],
    [
      "lem-weil-scalar-extension-composition",
      "lem-weil-scalar-extension-exact-triangulated"
    ],
    [
      "def-weil-algebraically-closed-coefficients"
    ]
  ],
  "consumer_eligible_after_all_repairs": true
}
```

The first repair frontier contains integral triangulation and scalar-extension constructibility; linearity follows triangulation, rationalization follows those three, composition and exactness follow rationalization, and the common-stage category follows both. The original consumer becomes eligible after these interfaces are supplied. No failure threshold, waiting flag, skip rule, retry backoff or dispatcher state is changed. Retire the stale consumer claim only after its current worker exits naturally.

Original files have sibling backups ending `.maint-Q22-coefficients-1792136951.bak`. Commit these metadata changes in both the authoritative shared DAG and the side project under their merge locks, using the requested Bin Wu identity, so side sync cannot restore false readiness. No Lean file changed; no compiler or global build is required for this metadata repair.
