## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.indEtale_strictLocal_invariance`
with the DAG's three-step assembly. Its public signature and existing docstring
are unchanged. No existing definition, public import, or other module changes.
A declaration-local unused-variable linter setting preserves the original named
`hbar` binder inside the result's universal quantifier; that name is unused in
the conclusion, and tactic introductions do not count as references to it.

The proof privately imports `Sheaf.AlgebraicGeometry.StrictLocalComparisonIndEtale`
and `Sheaf.AlgebraicGeometry.LocallyIndEtaleBaseChangeCharts`. Four proved private
helpers handle ring-equivalence transport to `IndEtaleAcrossUniverses`, the
chart comparison followed by Olivier, and selection of a chart at a geometric
point. The ring comparison uses `Spec.preimage` of the existing canonical map,
so the resulting isomorphisms have exactly the required structural and
evaluation equations. The arbitrary-base-change clause applies the existing
chart theorem. The structural-map clause applies the comparison to the identity
of the base, obtains an ind-etale affine factorization, and applies the same
chart argument at the canonical closed geometric lift.

Updated the item's node proof and proof origin to describe this Lean assembly.
The existing dependency and unit route is preserved. Both new proof imports
pass `tools/import_direction.py may`. Search by LeanFinder,
Loogle, Mathlib grep, and repository grep found no shorter existing invariance
theorem. The local Stacks sources verify the ind-etale-to-weakly-etale clause
and the hypotheses of Olivier's theorem.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Scheme.indEtale_strictLocal_invariance`
(node `lem-trf-ind-etale-strict-local-invariance`).

The item now contains zero `sorry`s. Added zero holes and zero split-off
statements. All four private helpers have complete proofs. The complete proof compiled in
3.6 seconds before the declaration-local linter cleanup; delivery checks compile
the final version and probe all its declarations.

This is a proof from the existing declared dependencies, including the currently
unproved `AlgebraicGeometry.Scheme.strictLocalComparison_indEtale`
(node `lem-trf-strict-local-comparison-ind-etale`) and
`AlgebraicGeometry.locally_indEtale_base_change_charts`
(node `lem-trf-locally-ind-etale-base-change-charts`). These existing holes are
not copied or added by this delivery.

## No longer needed

Removed these redundant direct proof imports:

- `Mathlib.AlgebraicGeometry.Pullbacks`: the existing public imports and the
  base-change-chart module already supply the pullback API.
- `Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale`: the declared
  strict-local comparison packages the chart factorization and ind-etaleness;
  this parent does not repeat that proof.
- `Sheaf.Paper.StrictHenselizationFunctoriality`: the canonical-map interface is
  already public through the unchanged `StrictHenselizationClosedLift` import.
- `Sheaf.RingTheory.IndEtaleStability`: only its weak-etaleness clause is needed,
  already available as the proved upstream `RingHom.IndEtale.weaklyEtale`.
- The duplicate private import of
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`: the
  unchanged public import already supplies it.

Removed obsolete direct tool approvals for
`lem-weil-pbc-fibre-product-affine-spectra` and
`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`. Their mathematics is
encapsulated in the declared base-change-chart and ring-comparison lemmas;
the parent no longer carries out those constructions directly. Neither module
is withdrawn: dependencies used by those lower lemmas remain needed. No node,
module, or source-library declaration is deleted, and no global module pruning
is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The checked-in imports still reflected
rebuilding the comparison and base-change charts, whereas the current DAG
already states those two pieces separately. The implementation now follows
that DAG. Its universe-transport predicate requires explicit transport to
ULift rings and descent of weak etaleness, supplied by proved private glue.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
