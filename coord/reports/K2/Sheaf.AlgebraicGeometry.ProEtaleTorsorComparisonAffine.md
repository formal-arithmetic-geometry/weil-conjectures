## What changed

Proved `AlgebraicGeometry.ProEtale.torsor_comparison_affine` with its exact existing
signature. Added proved private helpers for action reflection, torsor reflection,
trivialization by a section, restriction of sections, comparison/restriction compatibility,
transport along an isomorphism, local classicality, and an affine etale section cover.
All public definitions, instances, signatures and visibility are unchanged.

The shorter route uses the already proved `proEtale_locallyClassical_etaleCover`:
local torsor sections make the torsor locally isomorphic to the classical group;
local classicality supplies an etale model; full faithfulness descends the action and
reflects both torsor axioms. The finite affine cover is combined using the existing
`AffineProEt.sigmaCover` and `exists_sigmaCover_glue`, then the comparison unit returns
the glued section to the etale sheaf. This avoids choosing any data from an arbitrary
unproved existence theorem: all private data constructions are explicit, and the
model comes from an existing proved theorem.

Added proof imports `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`,
`WeilConjectures.AlgebraicGeometry.ProEtale.SigmaCover`,
`Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`,
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage`, and
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`.
Retained `Sheaf.AlgebraicGeometry.ProEtaleComparisonSections` for the unit interface.
Updated the theorem docstring and its DAG node to record this route.

Validation: server single-file compilation passed for the complete proof and after
import pruning, with no errors or warnings. On this resumption, compilation against the
current server library passed again in 4.8 seconds with no diagnostics. The final
delivery preflight supplies an independent compiler and axiom probe. The empty base, empty finite family and
arbitrary universe are included; the finite index is ULift (Fin n). No commutativity
is assumed or used. The general local-classicality module's imports do not reach this
item, as checked by import_direction.py.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.torsor_comparison_affine`
(node `det-pe-torsor-comparison-affine`). Added zero holes; zero holes remain in the
item or elsewhere in this delivery. All nine private helpers are proved.
The theorem still uses the existing `proEtaleClassicalSheavesImage` declaration,
whose proof is a separate project's obligation; no axioms are introduced here.

## No longer needed

Removed original proof imports:
- `Sheaf.RingTheory.IndEtaleStability`;
- `Sheaf.RingTheory.IndPrincipalZariski`;
- `Sheaf.CategoryTheory.SetSheafCoverDescent`;
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (available through the retained
  public and proof imports);
- `Sheaf.RingTheory.IndEtaleUniverseTransport` (the new argument does not use an
  ind-etale presentation);
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine` (already public
  through ClassicalContinuityMap).

The proof does not need the separate original obligations
`lem-weil-pbc-weakly-etale-source-locality`, `sk-thm-pe-indetale-refinement`,
`lem-weil-pbc-ind-etale-stability`, `def-weil-pbc-ind-etale-algebra`,
`lem-weil-pbc-faithfully-flat-surjective-spectrum`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-etale-base-change-finite-limits`,
`lem-weil-pbc-filtered-colimit-sets-elementwise`, and
`lem-pe-set-sheaf-cover-descent`. Their affine refinement, transition-cocycle
and gluing work is subsumed by the existing proved general local-classicality theorem.
This removes the need to import their statement modules for this item's proof;
some remain transitive implementation dependencies of the library's general results.
The existing comparison-sections import stays because its proved comparison-unit
isomorphism supplies full faithfulness and the invertible section map.

Removed obsolete top-level tool_uses entries
`lem-weil-pbc-ind-etale-stability`, `def-weil-pbc-ind-etale-algebra`, and
`lem-weil-pbc-comparison-sections`: the new direct section interface is the proved
`lem-weil-pbc-proetale-comparison-unit-sets`. No tool approvals were added or reordered.

## Where the brief, the DAG or earlier work was wrong

The planned cocycle argument is valid but unnecessary given the existing general
local-classicality theorem (Bhatt--Scholze Lemma 5.1.4), whose module is already proved.
The unit record `sk-lem-pe-torsor-comparison` has no realized statement or proof-step
nodes; its `realized.statement` and sole `realized.steps` entry are empty. The unit's
torsor-comparison statement is proved unchanged, and the affine comparison item
remains available to its parent. Below that statement, the shorter proof reuses the
general continuity/descent argument and proves the action descent explicitly.

The comparison/pullback node currently records an alternative support-site interface;
this proof uses the canonical original-site `comparisonCoefficientPullbackIso` in
`ComparisonPullbackCoherence`, already used by the local-classicality theorem's
continuity module. It compiles with this item's exact original-site comparison functor.
No dependency interface repair, downstream adaptation, new node or change record
is necessary.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
