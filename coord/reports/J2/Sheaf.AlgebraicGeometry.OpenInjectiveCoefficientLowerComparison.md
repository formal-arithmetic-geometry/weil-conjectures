## What changed

Added `OpenInjectiveCoefficientLowerComparisonFactorization`, isolating the derived mate
factorization needed by the target. The target theorem now combines this factorization with
`BaseChangeProperty` and the isomorphism of the derived unit on an injective single complex.
Repaired the factorization node metadata by removing its unused
`BaseChangeProperty` dependency from `stmt_deps`, `proof_deps`, and the proof step.

## Proved and sorry left

`AlgebraicGeometry.Etale.open_injective_coefficient_lower_comparison` is proved from the
factorization theorem and `BaseChangeProperty`.

One sorry remains in
`AlgebraicGeometry.Etale.open_injective_coefficient_lower_comparison_factorization`, node
`lem-sbc-open-injective-coefficient-lower-comparison-factorization`. It is the strict
intermediate mate-identification statement described in its docstring.

## No longer needed

The factorization node no longer depends on `sbc-def-base-change-property`; the target node
continues to use that dependency. No Lean imports were removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted a standalone Lean interface for the derived mate calculation.
The factorization node supplies that missing interface without changing the target statement. Change record: `coord/changes/open-injective-coefficient-lower-comparison-factorization.md`.

## New nodes

`lem-sbc-open-injective-coefficient-lower-comparison-factorization` records the strict
intermediate equality used by the target proof.

## Earlier second reading (a previous round; superseded)

1. **Interface and statement preservation.** I diffed the item module against the repository
version. The target theorem signature is byte-for-byte unchanged; the added imports and proof
only change its implementation. The new factorization theorem is a separate intermediate
equality and does not restate the target's `IsIso` conclusion.

2. **Compilation and proof status.** Both sandbox modules compile with `lcompile.py --all`.
There are no axioms, `unsafe`, `opaque`, `extern`, or hollow definitions. The only remaining
`sorry` is the named factorization theorem, whose docstring gives the mate-computation proof
and whose matching split node is present.

3. **Truth and strength of the split statement.** The factorization equality is the strict
derived-mate identification required before applying `BaseChangeProperty`; it is stronger in
form (an equality of maps) but narrower in scope (an injective single coefficient), so it is a
genuine reduction rather than a renamed target. Its hypotheses and conclusion match the code
and the source's closed-open derived calculation.

4. **Dependencies and pruning.** The target uses the factorization theorem, the derived
single-unit comparison, and the derived base-change comparison. The extra derived-comparison
dependency in the factorization module is proof-only; imports marked `public` are limited to
those needed by public statements. No old proof dependency is unused, so no DAG node or import
was pruned.

5. **Unit route and DAG agreement.** The target and factorization nodes remain in
`sk-lem-failure-field`; their Lean declarations, proof dependencies, source, and split status
agree with the delivered files. The unit's route is preserved.

I changed the factorization docstring to record the complete intended proof route (rewrite by
`baseChange_eq_derivedBaseChangeMapPlus`, apply the derived mate computation, and use naturality
and triangle identities), while leaving its statement and proof hole unchanged.


## Second reading by J2

1. **Interface and statement preservation.** I diffed the delivered target module against
`lean/Sheaf/AlgebraicGeometry/OpenInjectiveCoefficientLowerComparison.lean`. The target
signature is byte-for-byte unchanged. The added factorization declaration is a separate
homology-map equality and does not restate the target's `IsIso` conclusion. The repository
has no pre-existing declaration with either delivered name.

2. **Compilation and proof status.** `lcompile.py --all` compiles both delivered modules
without errors or warnings. There are no `axiom`, `unsafe`, `opaque`, `extern`,
`implemented_by`, or hollow definitions. The target and the factorization theorem each
have only the expected `sorryAx` inherited from the explicitly named factorization hole;
no other `sorry` remains.

3. **Truth and strength of the split statement.** The split theorem identifies the displayed
unit/pullback/counit homology map with the composite of the single-complex derived unit and
the base-change map. It is a strict equality at the intermediate map level, with fewer
hypotheses than the target and no `IsIso` conclusion, so it is a genuine reduction. Its
docstring gives the complete intended mate proof: rewrite by
`baseChange_eq_derivedBaseChangeMapPlus`, apply the derived mate computation, then use
naturality and the adjunction triangle identities. Edge cases such as arbitrary integer
`n` and zero coefficients are included by the polymorphic statement.

4. **Dependencies and pruning.** The target proof uses exactly the factorization theorem,
the injective single-complex unit isomorphism, and `BaseChangeProperty`; its proof-only
imports are plain `import`s. The factorization theorem's public imports are limited to
interfaces occurring in its statement, and its proof-only derived-comparison import is
plain. The unused `BaseChangeProperty` dependency was removed from the factorization node;
no further old proof dependency is unused.

5. **Unit route and DAG agreement.** Both declarations and their node metadata remain in
`sk-lem-failure-field`. The target node records the factorization reduction and
`BaseChangeProperty`; the factorization node records no base-change-property dependency.
The Lean statements, node statements, proof dependencies, source, split status, and unit
route agree. No target statement or definition was changed.

I changed only this report section; the proof modules and node metadata were already
consistent after the earlier repair.
