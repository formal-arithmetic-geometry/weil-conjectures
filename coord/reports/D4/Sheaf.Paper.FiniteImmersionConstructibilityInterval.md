## What changed

Proved `AlgebraicGeometry.Scheme.finiteImmersion_constructibility_interval` with its
entire original signature and all six conclusions unchanged. All four existing public
definitions and all public imports are unchanged. Only the assigned Lean module and its
DAG proof record change; no consumers require adaptation.

The private proved helpers convert the two existing local-constancy presentations,
transport constructibility across module isomorphisms, apply cartesian stratum restriction
to the actual pullback partitions, and assemble the given closed partition plus U.
The latter uses `sf_closed_partition_module_test`, converting its dependent-pair equalities
to isomorphisms over X and reindexing its Fin(n+1) by Fin n plus Unit. Positivity follows
from the added open index, without assuming any scheme or old stratum nonempty.

The already-proved `proEtaleIdentifiedOpenClosed` gives exact identified-coefficient closed
image and its invertible counit. `proEtaleRingModule_closed_essImage_iff_and_unit_isIso`
gives zero open restriction. The adjunction transpose identity in
`proEtaleConstantModulePullback_ring_direct` identifies the specified constant-section
scalar maps, yielding equality of the two published ordinary direct-image functors.
These two generic proved tools reuse the ringed open/closed argument rather than
reimplementing scalar transport. Neither replaces a unit step. The unit record's
`realized` arrays are empty; the finite-stage partition route is preserved.

`action_of_exact` uses the existing source-library `mapDerivedCategoryHomologyFunctorIso`
and `rightDerivedFunctorIsoMapDerivedCategory`, together with Mathlib's exact termwise
factorization and triangulated structure. Zero homology remains zero, so image support
is a subset of source support. This proves finite support and every unchanged interval;
constructibility is transported across the same natural homology comparison.
No bounded constructible-term resolution is used. A private abbreviation pins the existing
Mathlib Abelian instance at the module universe. Its instance attribute is confined to
an internal section; the final theorem uses local copies inside its proof.

Added private proof imports: CartesianStratumModuleRestriction, SfClosedPartitionModuleTest,
ProEtaleIdentifiedOpenClosed, ProEtaleClosedEssentialImage, the upstream
RightDerivedFunctor.MapDerivedCategory, and Mathlib.Logic.Equiv.Fin.Basic.
All new proof imports were checked for import cycles. Server single-file compilation
succeeds in approximately ten seconds. The final delivery preflight checks declarations
and axioms independently.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finiteImmersion_constructibility_interval`
(node `lem-sf-finite-immersion-constructibility-interval`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: 0.
No split-off statements or new axioms. The proof uses the already-stated cartesian-stratum
lemma, whose own proof remains an existing dependency item; this delivery does not claim
to prove that dependency or the complete target closure.

## No longer needed

Removed private imports:
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`;
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
- `Sheaf.CategoryTheory.SiteInverseImageTensor`;
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`;
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.

The proof no longer directly calls the separately recorded finite coefficient-ring map,
immersion all-limits, site tensor, or scheme-constructible-preimage lemmas. Exact pullback
is already provided by the ordinary-operations API; constructible preimages are packaged
by `Stratification.pullback`. Exact derivation is supplied by the proved source-library
comparison, so the removed ExactFunctorDerivedFunctor import is unnecessary. The DAG
retains the exact-derived-functor node for the mathematical comparison it describes.

Removed old direct proof dependencies `prop-weil-pbc-proetale-constant-ring-map`,
`lem-weil-pbc-proetale-immersion-limit-preservation`,
`lem-weil-pbc-proetale-ringed-open-closed`, and `lem-pur-scheme-constructible-preimage`.
Ringed localization remains a statement dependency and is used transitively by the proved
identified-coefficient tools. No module is withdrawn or asserted globally unreachable.

Deleted obsolete top-level tool approvals for
`lem-weil-pbc-noetherian-open-subscheme-noetherian`,
`prop-weil-pbc-proetale-constant-ring-map`,
`lem-weil-pbc-proetale-immersion-limit-preservation`,
`lem-weil-pbc-proetale-ringed-open-closed`, `lem-pur-scheme-constructible-preimage`,
`lem-weil-pbc-left-exact-site-inverse-image-tensor`, and
`lem-weil-pbc-proper-fp-permanence`. Existing retained approvals stay in their old order.
No upstream declarations or modules are removed. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was required. The existing imports did not yet
include either declared partition dependency. The closed partition dependency uses
`FiniteLocallyClosedStratification` and Fin(n+1), whereas this module uses `Stratification`
and Fin n plus Unit; the proof explicitly adapts both without changing any strata.
The cartesian dependency uses universe-general local constancy with a True model field;
explicit unpacking and repacking reconciles it with the original local-constancy predicate.
The library already has proved coefficient-transport and exact-derived comparisons,
so those parts need no new statements. All signatures and definitions remain unchanged.
The current blueprint finite-stage text has evolved since the node's cited snapshot;
this delivery proves the existing, stronger explicit partition assertion exactly and
does not alter the target or unit route. Edge cases are retained: empty schemes and
partitions, zero coefficients, nonreduced Z, and reversed intervals a>b.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
