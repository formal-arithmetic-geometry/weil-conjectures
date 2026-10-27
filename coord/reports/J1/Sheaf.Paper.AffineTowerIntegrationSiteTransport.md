## What changed

Proved `AlgebraicGeometry.ProEtale.VectorIntegrationSite.AffineTowerTransport.affineTowerIntegrationSiteTransport`.
The proof applies the existing `orderedIntegration_comparison` to the specified ordered
tower. It then proves the compactification,
refinement, open-restriction, invertibility and rank-zero clauses. Geometry is handled by
induction on the model family. Shifted finite Tate lines provide constructibility and
finite Tor amplitude on both sites; the published right-tower normal form handles inputs.
Generic proved helpers prevent repeated expansion of the derived-category structures
when specializing this argument to the finite coefficient ring.

The existing `orderedIntegration_comparison` (landed during this session) establishes
ordered trace comparison on every Noetherian base independently of the constant-input
line hypothesis. The theorem's statement and all trace constructions are unchanged.
Existing dependencies may themselves retain holes; no claim of axiom-free transitive
closure is made.

Single-file profiling identified the specialized indexed inductive `Model` as a kernel
and generated-recursion bottleneck before the proof helpers. `ModelFamily` expresses the least closed predicate by its elimination property,
and `Model` specializes it to exactly the same six closure rules.
The original introduction names are provided as proved wrappers. No downstream Lean
module uses this interface. See `coord/changes/J1-affine-tower-model-parameters.md`.

Updated the item's proof plan and proof dependencies to describe this Lean argument.
No other existing module is edited. Validation is through the required single-file
compiler and delivery preflight.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.AffineTowerTransport.affineTowerIntegrationSiteTransport`
(node `lem-pur-affine-tower-integration-site-transport`). There are zero `sorry`s left
in the delivery, zero added holes, and zero split-off statements. All private helpers
are proved. The complete proof compiled in a profiled single-file check (53.0 seconds after factoring the generic conversions);
the final clean module check and delivery preflight supply the final validation.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin`

The proof no longer directly uses these old proof dependencies:

- `def-exchange-projection`
- `def-pur-finite-site-tensor-projection`
- `def-pur-proetale-affine-line-counit`
- `def-pur-proetale-projection-integration`
- `def-weil-pbc-composite-adjunction`
- `def-weil-proper-morphism`
- `lem-amb-finite-tate-site-descent`
- `lem-amb-proper-coproducts-projection`
- `lem-asd-etale-finite-twist-pullback`
- `lem-cbc-compactifiable-cofiltered`
- `lem-cbc-extension-zero-projection-formula`
- `lem-pur-etale-open-derived-tensor`
- `lem-pur-projection-comparison-etale-origin`
- `lem-weil-finite-compact-projection-formula`

The existing ordered-comparison theorem packages the line and tower argument.
The compactification cocycle and site squares supply completion independence directly.
Generic exact site-comparison results preserve the explicit Tor intervals and
constructibility; their role is retained under `lem-sf-comparison-tor-amplitude`.
These removals concern direct use by this item. Several remain in public trace
definitions or in the reused comparison theorem's dependencies. No whole module is
withdrawn or claimed to leave the targets' closure.

Removed the obsolete tool approvals for the unused direct calculations: finite-twist
pullback, finite compact projection, proper projection, projection comparison,
common-refinement existence, and both open-tensor theorems. Public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The old Step 10 applies ordered comparison on an arbitrary open base, while the
constant-input `LineComparison` only quantifies over coordinate bases of the original
scheme. The proof uses the existing all-Noetherian `orderedIntegration_comparison`
on every open base. Its module was newly landed during this session; the final proof
reuses it and removes the duplicate projective-line and tower-induction calculations.
This fixes the gap without changing the theorem statement or assuming separatedness.

The compiler bottleneck was in the original concrete scheme-indexed Model family,
not in an unfinished proof. It is repaired by a least-closure representation with abstract operation
parameters, with exactly the same generated schemes. Empty bases, dimension zero,
arbitrary open restrictions, arbitrary compactifications, and ramified finite
coefficient rings remain included; no flatness over the Kummer ring is assumed.

Change record: `coord/changes/J1-affine-tower-model-parameters.md`.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
