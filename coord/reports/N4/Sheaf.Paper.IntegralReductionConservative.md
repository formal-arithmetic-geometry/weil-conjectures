## What changed

Restored the complete quarantined `Sheaf.Paper.IntegralReductionConservative` module.
Repaired `AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_reflects_isIso`
without changing its signature or public imports. Project the three closure instances
directly from `integralConstructible_serre`, and privately import the relocated
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
Explicitly install its `isTriangulated_boundedConstructible_of_serre` instance using
these coefficient-dependent closures before forming the constructible cone.

The rest of the existing cone, scalar reduction, homology and Nakayama argument is
preserved. The file compiles through lcompile.py without errors or warnings (13.6 seconds).
The existing node's proof and all four proof dependencies still describe this proof;
its Lean attachment is preserved. No new statements, definitions or nodes are needed.

## Proved and sorry left

This is a zero-hole quarantined compile repair. The archived module contained zero
`sorry`; the restored module contains zero `sorry`. Holes closed: none (0 of 0).
Holes added: none. Split off: none.

`AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_reflects_isIso`
(lem-weil-pbc-integral-reduction-conservative) has a complete compiling proof from the
existing named dependency declarations. No dependency proof is replaced or duplicated.

## No longer needed

None. No import, declaration, module or node is removed or withdrawn. All four recorded
proof dependencies remain needed: integral Serre closure, conditional triangulated
closure, scalar reduction, and constructible Nakayama. The relocated conditional
triangulated theorem is now imported explicitly and applied directly.

## Where the brief, the DAG or earlier work was wrong

The archived proof relied on the conditional triangulated API being available through
old transitive imports. After the upstream sync, that API lives in the separate
UpstreamExtra module. Unpacking the private-imported closure theorem with `obtain`
failed at `generalize`; direct projections then exposed the missing closure-predicate
visibility. The explicit private import supplies those predicates and the actual
conditional triangulated theorem. The proof deliberately installs that conditional
instance, rather than relying on the source's noetherian-only instance.

No mathematical statement or unit route was changed. This packet restores the exact
quarantined item and does not delete its archive or its DAG attachment.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
